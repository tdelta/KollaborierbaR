const getSyntax = (lang) => {
    return {
        // defining various JML keywords etc.
        'keywords': {
            'behavior_keyword':
                lang.arrayToMap(
                /*  ^ will convert the array below into a map, since maps allow for
                    much more efficient lookups */
                    ('behavior|normal_behavior|exceptional_behavior|behaviour|normal_behaviour|exceptional_behaviour')
                        .split('|')
                    // ^results in an array of keywords, by splitting the string at |
                    // We use this notation, since its common for grammars.
                ),

            'java_visibility_keyword': lang.arrayToMap(
                ('public|protected|private').split('|')),
            'requires_keyword': lang.arrayToMap(
                ('requires|pre|requires_redundantly|pre_redundantly').split('|')),
            'ensures_keyword': lang.arrayToMap(
                ('ensures|post|ensures_redundantly|post_redundantly').split('|')),
            'signals_keyword': lang.arrayToMap(
                ('signals|signals_redundantly|exsures|exsures_redundantly').split('|')),
            'signals_only_keyword': lang.arrayToMap(
                ('signals_only|signals_only_redundantly').split('|')),
            'diverges_keyword': lang.arrayToMap(
                ('diverges|diverges_redundantly').split('|')),
            'when_keyword': lang.arrayToMap(
                ('when|when_redundantly').split('|')),
            'assignable_keyword': lang.arrayToMap(
                ('assignable|assignable_redundantly|modifiable|modifiable_redundantly|modifies|modifies_redundantly').split('|')),
            'accessible_keyword': lang.arrayToMap(
                ('accessible|accessible_redundantly').split('|')),
            'callable_keyword': lang.arrayToMap(
                ('callable|callable_redundantly').split('|')),
            'measured_by_keyword': lang.arrayToMap(
                ('measured_by|measured_by_redundantly').split('|')),
            'captures_keyword': lang.arrayToMap(
                ('captures|captures_redundantly').split('|')),
            'working_space_keyword': lang.arrayToMap(
                ('working_space|working_space_redundantly').split('|')),
            'duration_keyword': lang.arrayToMap(
                ('duration|duration_redundantly').split('|')),
            'other_keyword': lang.arrayToMap(
                'abrupt_behavior|abrupt_behaviour|also|assert_redundantly|assume|assume_redundantly|axiom|breaks|breaks_redundantly|choose|choose_if|code|code_bigint_math||code_java_math|code_safe_math|constraint|constraint_redundantly|constructor|continues|continues_redundantly|decreases|decreases_redundantly|decreasing|decreasing_redundantly|example|exceptional_example|extract|field|forall|for_example|ghost|helper|hence_by|hence_by_redundantly|implies_that|in|in_redundantly|initializer|initially|instance|invariant|invariant_redundantly|loop_invariant|loop_invariant_redundantly|maintaining|maintaining_redundantly|maps|maps_redundantly|method|model|model_program|monitored|monitors_for|non_null|normal_example|nowarn|nullable|nullable_by_default|old|or|pure|readable|refining|represents|represents_redundantly|returns|returns_redundantly|set|signals_only|signals_only_redundantly|spec_bigint_math|spec_java_math|spec_protected|spec_public|spec_safe_math|static_initializer|uninitialized|unreachable|writable'.split('|')),
        },
        'predicates' : {
            'predicate_keyword': lang.arrayToMap(
                ('\\TYPE|\\bigint|\\bigint_math|\\duration|\\elemtype|\\everything|\\exists|\\forall|\\fresh|\\into|\\invariant_for|\\is_initialized|\\java_math|\\lblneg|\\lblpos|'+
                '\\lockset|\\max|\\min|\\nonnullelements|\\not_assigned|\\not_modified|\\not_specified|\\nothing|\\nowarn|\\nowarn_op|\\num_of|\\old|\\only_accessed|\\only_assigned|'+
                '\\only_called|\\only_captured|\\pre|\\product|\\reach|\\real|\\result|\\same|\\safe_math|\\space|\\such_that|\\sum|\\typeof|\\type|\\warn_op|\\warn|\\working_space').split('|')),
        },
        'types': {
            'java_datatype': lang.arrayToMap(
                'boolean|byte|char|short|int|long'.split('|')
            ),
        },
        'operators': lang.arrayToMap(
            '|<|>|!|~|?|:|==|<=|>=|!=|&&|++|--|+|-|*|/|&|^|%|<<|>>|>>>|+=|-=|*=|/=|&=|`|=\'|^=|%=|<<=|>>=|>>>=|='
                .split('|')
                .concat(['|','||'])
        ),
        'special_symbols': lang.arrayToMap(
            '==>|<==|<==>|<=!=>|->|<-|<:|..|{|}|<#|<#='
                .split('|')
        )
    };
};

export default getSyntax;
