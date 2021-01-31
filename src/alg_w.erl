%%% A short Algorithm W implementation in Erlang.

-module(alg_w).

-export([infer/1, infer/2, pprint/1]).
-export_type([expr/0, lit/0, type/0, scheme/0, type_env/0]).

-compile({no_auto_import, [apply/2]}).

%% -----------------------------------------------------------------------------
%% Public API
%% -----------------------------------------------------------------------------

-type expr() :: {e_var, atom()}
              | {e_lit, lit()}
              | {e_app, expr(), expr()}
              | {e_abs, atom(), expr()}
              | {e_let, atom(), expr(), expr()}.

-type lit() :: {l_int, integer()}
             | {l_bool, boolean()}.

-type type() :: {t_var, atom()}
              | t_int
              | t_bool
              | {t_fun, type(), type()}.

-type scheme() :: {scheme, [atom()], type()}.

-type type_env() :: {type_env, #{atom() => scheme()}}.

%% Entrypoint for type inference.
-spec infer(expr()) -> {ok, type()} | {error, string()}.
infer(E) ->
  infer(E, {type_env, #{}}).

%% Entrypoint for type inference with an existing type environment.
-spec infer(expr(), type_env()) -> {ok, type()} | {error, string()}.
infer(E, {type_env, Env}) ->
  try ti(new_state(), {type_env, Env}, E) of
    {_, S, T} -> {ok, apply(S, T)}
  catch
    throw:{infer_err, Message} -> {error, Message}
  end.

%% Pretty printer.
-spec pprint(type() | expr() | lit() | scheme()) -> string().
pprint(X) ->
  lists:flatten(pprint(X, 0)).

%% -----------------------------------------------------------------------------
%% Helper Functions
%% -----------------------------------------------------------------------------

-type types() :: type()
               | scheme()
               | type_env()
               | [types()].

-type subst() :: #{atom() => type()}.

%% Get the free type variables of a type.
-spec ftv(types()) -> ordsets:set(atom()).
ftv({t_var, Name}) ->
  ordsets:from_list([Name]);
ftv(t_int) ->
  ordsets:new();
ftv(t_bool) ->
  ordsets:new();
ftv({t_fun, T1, T2}) ->
  ordsets:union(ftv(T1), ftv(T2));
ftv({scheme, Vars, T}) ->
  ordsets:subtract(ftv(T), ordsets:from_list(Vars));
ftv({type_env, Env}) ->
  ftv(maps:values(Env));
ftv(List) when is_list(List) ->
  lists:foldl(fun ordsets:union/2, ordsets:new(), lists:map(fun ftv/1, List)).

%% Substitute free type variables.
-spec apply(subst(), Types) -> Types when Types :: types().
apply(S, {t_var, Name} = Var) ->
  case S of
    #{Name := T} -> T;
    _            -> Var
  end; 
apply(_, t_int) ->
  t_int;
apply(_, t_bool) ->
  t_bool;
apply(S, {t_fun, T1, T2}) ->
  {t_fun, apply(S, T1), apply(S, T2)};
apply(S, {scheme, Vars, T}) ->
  {scheme, Vars, apply(maps:without(Vars, S), T)};
apply(S, {type_env, Env}) ->
  {type_env, maps:map(fun(_, V) -> apply(S, V) end, Env)};
apply(S, List) when is_list(List) ->
  lists:map(fun(T) -> apply(S, T) end, List).

%% Blank substitution.
-spec null_subst() -> subst().
null_subst() ->
  #{}.

%% Compose substitutions.
-spec compose_subst(subst(), subst()) -> subst().
compose_subst(S1, S2) ->
  maps:merge(maps:map(fun(_, V) -> apply(S1, V) end, S2), S1).

%% Abstract a type over all type vars free in the type but not the type env.
-spec generalize(type_env(), type()) -> scheme().
generalize(Env, T) ->
  Vars = ordsets:to_list(ordsets:subtract(ftv(T), ftv(Env))),
  {scheme, Vars, T}.

%% Type inference state.
-record(state, {counter :: counters:counters_ref()}).

%% Create a new type inference state.
-spec new_state() -> #state{}.
new_state() ->
  #state{counter = counters:new(1, [])}.

%% Create a new type variable.
-spec new_ty_var(#state{}, string()) -> {#state{}, type()}.
new_ty_var(State, Prefix) ->
  ok = counters:add(State#state.counter, 1, 1),
  Num = counters:get(State#state.counter, 1) - 1,
  TVar = {t_var, list_to_atom(Prefix ++ integer_to_list(Num))},
  {State, TVar}.

%% Replace bound type vars in a type scheme with fresh type vars.
-spec instantiate(#state{}, scheme()) -> {#state{}, type()}.
instantiate(State, {scheme, Vars, T}) ->
  {SList, NewState} = lists:mapfoldl(fun(Var, CurrState) ->
    {NextState, NewT} = new_ty_var(CurrState, "a"),
    {{Var, NewT}, NextState}
  end, State, Vars),
  S = maps:from_list(SList),
  {NewState, apply(S, T)}.

%% Get the most general unifier.
-spec mgu(#state{}, type(), type()) -> {#state{}, subst()}.
mgu(State, {t_fun, L1, R1}, {t_fun, L2, R2}) ->
  {State1, S1} = mgu(State, L1, L2),
  {State2, S2} = mgu(State1, apply(S1, R1), apply(S1, R2)),
  {State2, compose_subst(S2, S1)};
mgu(State, {t_var, Name}, T) ->
  var_bind(State, Name, T);
mgu(State, T, {t_var, Name}) ->
  var_bind(State, Name, T);
mgu(State, t_int, t_int) ->
  {State, null_subst()};
mgu(State, t_bool, t_bool) ->
  {State, null_subst()};
mgu(_, T1, T2) ->
  throw({infer_err, "types do not unify: " ++ pprint(T1) ++ " vs. " ++ pprint(T2)}).

%% Bind a type to a variable.
-spec var_bind(#state{}, atom(), type()) -> {#state{}, subst()}.
var_bind(State, U, {t_var, U}) ->
  {State, null_subst()};
var_bind(State, U, T) ->
  case ordsets:is_element(U, ftv(T)) of
    true ->
      throw({infer_err, "occurs check fails: " ++ atom_to_list(U) ++ " vs. " ++ pprint(T)});
    false ->
      {State, #{U => T}}
  end.

%% Infer types for literals.
-spec ti_lit(#state{}, lit()) -> {#state{}, subst(), type()}.
ti_lit(State, {l_int, _}) ->
  {State, null_subst(), t_int};
ti_lit(State, {l_bool, _}) ->
  {State, null_subst(), t_bool}.

%% Infer types for expressions.
%%
%% The type environment must have bindings for all free variables in the
%% expression. The substition returned gives the type constraints imposed on
%% type variables by the expression, and the type given is the type inferred for
%% the expression.
-spec ti(#state{}, type_env(), expr()) -> {#state{}, subst(), type()}.
ti(State, {type_env, Env}, {e_var, N}) ->
  case Env of
    #{N := Sigma} ->
      {NewState, T} = instantiate(State, Sigma),
      {NewState, null_subst(), T};
    _ ->
      throw({infer_err, "unbound variable: " ++ atom_to_list(N)})
  end;
ti(State, _, {e_lit, L}) ->
  ti_lit(State, L);
ti(State, {type_env, Env}, {e_abs, N, E}) ->
  {State2, TV} = new_ty_var(State, "a"),
  Env2 = Env#{N => {scheme, [], TV}},
  {State3, S1, T1} = ti(State2, {type_env, Env2}, E),
  {State3, S1, {t_fun, apply(S1, TV), T1}};
ti(State, {type_env, Env}, Expr = {e_app, E1, E2}) ->
  try begin
    {State2, TV} = new_ty_var(State, "a"),
    {State3, S1, T1} = ti(State2, {type_env, Env}, E1),
    {State4, S2, T2} = ti(State3, apply(S1, {type_env, Env}), E2),
    {State5, S3} = mgu(State4, apply(S2, T1), {t_fun, T2, TV}),
    {State5, S1, S2, S3, TV}
  end of
    {NewState, S1_, S2_, S3_, TV_} ->
      {NewState, compose_subst(compose_subst(S3_, S2_), S1_), apply(S3_, TV_)}
  catch
    throw:{infer_err, Message} ->
      throw({infer_err, Message ++ "\n in " ++ pprint(Expr)})
  end;
ti(State, {type_env, Env}, {e_let, X, E1, E2}) ->
  {State2, S1, T1} = ti(State, {type_env, Env}, E1),
  Env2 = Env#{X => generalize(apply(S1, {type_env, Env}), T1)},
  {State3, S2, T2} = ti(State2, apply(S1, {type_env, Env2}), E2),
  {State3, compose_subst(S2, S1), T2}.

%% pprint/2 implementation.

%% type().
pprint({t_var, N}, _) ->
  atom_to_list(N);
pprint(t_int, _) ->
  "Int";
pprint(t_bool, _) ->
  "Bool";
pprint({t_fun, {t_fun, _, _} = T, S}, Indent) ->
  ["(", pprint(T, Indent), ") -> ", pprint(S, Indent)];
pprint({t_fun, T, S}, Indent) ->
  [pprint(T, Indent), " -> ", pprint(S, Indent)];

%% expr().
pprint({e_var, Name}, _) ->
  atom_to_list(Name);
pprint({e_lit, Lit}, Indent) ->
  pprint(Lit, Indent);
pprint({e_let, X, B, Body}, Indent) ->
  Padding = lists:duplicate(Indent + 2, $\s),
  ["let ", atom_to_list(X), " = ", pprint(B, Indent), " in\n", Padding, pprint(Body, Indent + 2)];
pprint({e_app, E1, E2}, Indent) when element(1, E2) =:= e_let;
                                     element(1, E2) =:= e_app;
                                     element(1, E2) =:= e_abs ->
  [pprint(E1, Indent), " (", pprint(E2, Indent), ")"];
pprint({e_app, E1, E2}, Indent) ->
  [pprint(E1, Indent), " ", pprint(E2, Indent)];
pprint({e_abs, N, E}, Indent) ->
  [$\\, atom_to_list(N), " -> ", pprint(E, Indent)];

%% lit().
pprint({l_int, I}, _) ->
  integer_to_list(I);
pprint({l_bool, true}, _) ->
  "True";
pprint({l_bool, false}, _) ->
  "False";

%% scheme().
pprint({scheme, Vars, T}, Indent) ->
  ["All ", lists:join($,, lists:map(fun atom_to_list/1, Vars)), ". ", pprint(T, Indent)].
