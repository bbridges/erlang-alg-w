-module(alg_w_tests).

-include_lib("eunit/include/eunit.hrl").

alg_w_test_() ->
  [
    % let id = \x -> x in
    %   id
    % (a1 -> a1).
    ?_assertMatch(
      {ok, {t_fun, {t_var, a1}, {t_var, a1}}},
      alg_w:infer(
        {e_let, id, {e_abs, x, {e_var, x}},
                    {e_var, id}}
      )
    ),
    % let id \x -> x in
    %   id id
    % (a3 -> a3).
    ?_assertMatch(
      {ok, {t_fun, {t_var, a3}, {t_var, a3}}},
      alg_w:infer(
        {e_let, id, {e_abs, x, {e_var, x}},
                    {e_app, {e_var, id}, {e_var, id}}}
      )
    ),
    % let id \x -> let y = x in
    %                y in
    %   id id
    % (a3 -> a3).
    ?_assertMatch(
      {ok, {t_fun, {t_var, a3}, {t_var, a3}}},
      alg_w:infer(
        {e_let, id, {e_abs, x, {e_let, y, {e_var, x},
                                          {e_var, y}}},
                    {e_app, {e_var, id}, {e_var, id}}}
      )
    ),
    % let id \x -> let y = x in
    %                y in
    %   id id 2
    % (Int).
    ?_assertMatch(
      {ok, t_int},
      alg_w:infer(
        {e_let, id, {e_abs, x, {e_let, y, {e_var, x},
                                          {e_var, y}}},
                    {e_app, {e_app, {e_var, id}, {e_var, id}}, {e_lit, {l_int, 2}}}}
      )
    ),
    % let id \x -> x x in
    %   id
    % error.
    ?_assertMatch(
      {error, "occurs check fails: a0 vs. a0 -> a1\n in x x"},
      alg_w:infer(
        {e_let, id, {e_abs, x, {e_app, {e_var, x}, {e_var, x}}},
                    {e_var, id}}
      )
    ),
    % \m -> let y = m in
    %         let x = y True in
    %           x
    % ((Bool -> a1) -> a1).
    ?_assertMatch(
      {ok, {t_fun, {t_fun, t_bool, {t_var, a1}}, {t_var, a1}}},
      alg_w:infer(
        {e_abs, m, {e_let, y, {e_var, m},
                              {e_let, x, {e_app, {e_var, y}, {e_lit, {l_bool, true}}},
                                         {e_var, x}}}}
      )
    ),
    % 2 2
    % error.
    ?_assertMatch(
      {error, "types do not unify: Int vs. Int -> a0\n in 2 2"},
      alg_w:infer(
        {e_app, {e_lit, {l_int, 2}}, {e_lit, {l_int, 2}}}
      )
    )
  ].
