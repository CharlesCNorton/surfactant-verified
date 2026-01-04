/****************************************************************************
 * Surfactant Decision Logic - Promela Model for SPIN Verification
 *
 * Translated from Coq formalization (surfactant.v)
 * Verifies temporal properties of surfactant therapy state machine.
 *
 * Author: Charles C. Norton
 * Date: January 2026
 *
 * Usage:
 *   spin -a surfactant.pml
 *   gcc -o pan pan.c
 *   ./pan -a              # Verify all LTL properties
 *   ./pan -a -N p_safe    # Verify specific property
 ****************************************************************************/

/****************************************************************************
 * CONSTANTS - from surfactant.v
 ****************************************************************************/

/* Timing constraints (in minutes) */
#define SURFACTANT_WINDOW_MAX    120   /* 2 hours from RDS onset */
#define RESPONSE_EVAL_MIN        120   /* 2 hours post-dose minimum */
#define RESPONSE_EVAL_MAX        360   /* 6 hours post-dose maximum */
#define REPEAT_INTERVAL_MIN      360   /* 6 hours between doses */
#define MAX_DOSES                4     /* Maximum surfactant doses */

/* Clinical thresholds */
#define FIO2_THRESHOLD           30    /* FiO2 > 30% triggers rescue */
#define GA_PROPHYLACTIC_DAYS     210   /* GA < 30 weeks = 210 days */
#define CPAP_MIN_PRESSURE        6     /* Minimum CPAP for rescue */

/****************************************************************************
 * STATE MACHINE LOCATIONS - TALocation from surfactant.v
 ****************************************************************************/

mtype = {
    TA_Initial,          /* Pre-diagnosis state */
    TA_RDS_Diagnosed,    /* RDS diagnosed, clock starts */
    TA_Evaluating,       /* Evaluating for surfactant */
    TA_Surfactant_Given, /* Surfactant administered */
    TA_Monitoring,       /* Post-dose monitoring */
    TA_Responded,        /* Good response, weaning */
    TA_NonResponder,     /* Poor response, consider repeat */
    TA_Weaned,           /* Successfully weaned */
    TA_Contraindicated   /* Contraindication present - blocked */
};

/****************************************************************************
 * PATIENT STATE
 ****************************************************************************/

typedef Patient {
    byte ga_weeks;           /* Gestational age weeks (22-42) */
    byte ga_days;            /* Gestational age days (0-6) */
    short weight_g;          /* Birth weight in grams */
    byte fio2;               /* Current FiO2 percentage */
    bool intubated;          /* Currently intubated */
    bool has_rds_signs;      /* >= 2 clinical signs */
    bool has_contraindication;
};

/****************************************************************************
 * GLOBAL STATE
 ****************************************************************************/

mtype location = TA_Initial;
byte clock = 0;                      /* Minutes since entering current state */
byte doses_given = 0;
byte time_since_last_dose = 0;
bool surfactant_indicated = false;
bool surfactant_given = false;

/* Patient instance */
Patient patient;

/* Nondeterministic environment */
bool env_rds_detected;
bool env_good_response;

/****************************************************************************
 * HELPER MACROS - Decision Logic from surfactant.v
 ****************************************************************************/

/* GA in total days */
#define GA_TOTAL_DAYS (patient.ga_weeks * 7 + patient.ga_days)

/* Prophylactic indication: GA < 30 weeks */
#define PROPHYLACTIC_INDICATED (GA_TOTAL_DAYS < GA_PROPHYLACTIC_DAYS)

/* Rescue indication: FiO2 > 30% with RDS signs */
#define RESCUE_INDICATED (patient.fio2 > FIO2_THRESHOLD && patient.has_rds_signs)

/* Overall surfactant indication */
#define SURFACTANT_INDICATED \
    (!patient.has_contraindication && (PROPHYLACTIC_INDICATED || RESCUE_INDICATED))

/* Timing guards */
#define WITHIN_SURFACTANT_WINDOW (clock <= SURFACTANT_WINDOW_MAX)
#define RESPONSE_EVAL_OK (clock >= RESPONSE_EVAL_MIN && clock <= RESPONSE_EVAL_MAX)
#define REPEAT_TIMING_OK (time_since_last_dose >= REPEAT_INTERVAL_MIN)
#define CAN_REPEAT (doses_given < MAX_DOSES && REPEAT_TIMING_OK)

/****************************************************************************
 * MAIN THERAPY PROCESS
 ****************************************************************************/

active proctype SurfactantTherapy() {

    /* Initialize patient with default values */
    patient.ga_weeks = 28;
    patient.ga_days = 0;
    patient.weight_g = 1000;
    patient.fio2 = 45;
    patient.intubated = true;
    patient.has_rds_signs = true;
    patient.has_contraindication = false;

    /* Main state machine loop */
    do
    :: location == TA_Initial ->
        /* Wait for RDS detection (nondeterministic) */
        if
        :: env_rds_detected ->
            location = TA_RDS_Diagnosed;
            clock = 0;
            printf("MSC: RDS diagnosed at GA %d+%d\n",
                   patient.ga_weeks, patient.ga_days);
        :: !env_rds_detected ->
            skip  /* Stay in initial */
        fi

    :: location == TA_RDS_Diagnosed ->
        /* Check for contraindication first */
        if
        :: patient.has_contraindication ->
            location = TA_Contraindicated;
            printf("MSC: Contraindication present - blocked\n");
        :: !patient.has_contraindication ->
            /* Move to evaluation */
            location = TA_Evaluating;
            surfactant_indicated = SURFACTANT_INDICATED;
            printf("MSC: Evaluating, indicated=%d\n", surfactant_indicated);
        fi

    :: location == TA_Evaluating ->
        /* Must act within window */
        if
        :: WITHIN_SURFACTANT_WINDOW && surfactant_indicated && patient.intubated ->
            /* Give surfactant */
            location = TA_Surfactant_Given;
            surfactant_given = true;
            doses_given++;
            clock = 0;
            time_since_last_dose = 0;
            printf("MSC: Surfactant dose %d given at %d min\n", doses_given, clock);
        :: WITHIN_SURFACTANT_WINDOW && !surfactant_indicated ->
            /* Not indicated, continue monitoring */
            clock++;
        :: !WITHIN_SURFACTANT_WINDOW ->
            /* Window expired - missed opportunity */
            printf("MSC: Window expired without surfactant\n");
            break
        fi

    :: location == TA_Surfactant_Given ->
        /* Immediately move to monitoring */
        location = TA_Monitoring;
        clock = 0;
        printf("MSC: Monitoring post-dose\n");

    :: location == TA_Monitoring ->
        /* Wait for response evaluation window */
        if
        :: clock < RESPONSE_EVAL_MIN ->
            clock++;
            time_since_last_dose++;
        :: RESPONSE_EVAL_OK ->
            /* Evaluate response (nondeterministic) */
            if
            :: env_good_response ->
                location = TA_Responded;
                printf("MSC: Good response at %d min post-dose\n", clock);
            :: !env_good_response ->
                location = TA_NonResponder;
                printf("MSC: Poor response at %d min post-dose\n", clock);
            fi
        :: clock > RESPONSE_EVAL_MAX ->
            /* Forced to evaluate */
            if
            :: env_good_response -> location = TA_Responded
            :: !env_good_response -> location = TA_NonResponder
            fi
        fi

    :: location == TA_Responded ->
        /* Good response - proceed to weaning */
        location = TA_Weaned;
        printf("MSC: Weaning initiated\n");

    :: location == TA_NonResponder ->
        /* Poor response - consider repeat dose */
        time_since_last_dose++;
        if
        :: CAN_REPEAT && patient.fio2 > FIO2_THRESHOLD ->
            /* Repeat dose */
            location = TA_Evaluating;
            surfactant_indicated = true;
            clock = 0;
            printf("MSC: Repeat dose indicated\n");
        :: doses_given >= MAX_DOSES ->
            /* Max doses reached */
            printf("MSC: Max doses reached (%d)\n", doses_given);
            break
        :: else ->
            skip  /* Wait for repeat interval */
        fi

    :: location == TA_Weaned ->
        /* Terminal state - success */
        printf("MSC: Successfully weaned\n");
        break

    :: location == TA_Contraindicated ->
        /* Terminal state - blocked */
        printf("MSC: Treatment blocked by contraindication\n");
        break
    od
}

/****************************************************************************
 * LTL PROPERTIES FOR VERIFICATION
 ****************************************************************************/

/* Property 1: Contraindication always blocks treatment */
ltl p_contra_blocks {
    [](patient.has_contraindication -> !surfactant_given)
}

/* Property 2: Surfactant never given after window expires
   (if we track when it was given relative to RDS onset) */
ltl p_window_respected {
    []((location == TA_Surfactant_Given) -> WITHIN_SURFACTANT_WINDOW)
}

/* Property 3: Response is always evaluated within valid window */
ltl p_response_timing {
    []((location == TA_Responded || location == TA_NonResponder) ->
       (clock >= RESPONSE_EVAL_MIN))
}

/* Property 4: Maximum doses never exceeded */
ltl p_max_doses {
    [](doses_given <= MAX_DOSES)
}

/* Property 5: Repeat doses respect minimum interval */
ltl p_repeat_interval {
    []((location == TA_Surfactant_Given && doses_given > 1) ->
       time_since_last_dose >= REPEAT_INTERVAL_MIN)
}

/* Property 6: If indicated and no contraindication, eventually treated or window expires */
ltl p_liveness {
    [](surfactant_indicated && !patient.has_contraindication ->
       <>(surfactant_given || !WITHIN_SURFACTANT_WINDOW))
}

/* Property 7: Well infant (GA >= 30w, FiO2 <= 30) never indicated */
ltl p_well_infant {
    []((GA_TOTAL_DAYS >= GA_PROPHYLACTIC_DAYS && patient.fio2 <= FIO2_THRESHOLD) ->
       !surfactant_indicated)
}

/* Property 8: Safety - no deadlock in valid states */
ltl p_no_deadlock {
    []<>(location == TA_Weaned || location == TA_Contraindicated ||
         doses_given >= MAX_DOSES)
}
