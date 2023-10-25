import data.real.basic
import data.real.pi.bounds
import analysis.special_functions.log

noncomputable theory

open real
open_locale real

variables (x y : ℝ)
variable n : ℤ 

notation `pi` := real.pi
notation `Abs` := has_abs.abs
infixr ` ** `:80  := has_pow.pow

lemma sin_eq_neg_sin_neg_add_int_mul_two_pi : sin x = - sin (-x + n * (2*pi)):=
begin
  rw sin_add_int_mul_two_pi _ _,
  rw sin_neg,
  rw neg_neg,
end

lemma cos_eq_cos_neg_add_int_mul_two_pi : cos x = cos (-x + n * (2*pi)):=
begin
  rw cos_add_int_mul_two_pi,
  rw cos_neg,
end

lemma tan_eq_neg_tan_neg_add_int_mul_pi : tan x = - tan (-x + n*pi):=
begin
  rw tan_add_int_mul_pi,
  rw tan_neg,
  rw neg_neg,
end

lemma sin_eq_sin_add_int_mul_two_pi : sin x = sin (x + n * (2*pi)) :=
begin
  rw sin_add_int_mul_two_pi,
end

lemma cos_eq_cos_add_int_mul_two_pi : cos x = cos (x + n*(2*pi)) :=
begin
  rw cos_add_int_mul_two_pi,
end

lemma sin_eq_neg_sin_add_int_mul_two_pi_add_pi : sin x = - sin(x + n * (2*pi) + pi) := 
begin
  rw ← sin_add_int_mul_two_pi x n,
  rw sin_add_pi _,
  rw neg_neg,
end

lemma cos_eq_neg_cos_add_int_mul_two_pi_add_pi : cos x = -cos(x+n*(2*pi)+pi):=
begin
  rw ← cos_add_int_mul_two_pi x n,
  rw cos_add_pi _,
  rw neg_neg,
end

lemma tan_eq_tan_add_int_mul_pi : tan x = tan(x + n*pi) :=
begin
  rw tan_add_int_mul_pi,
end

lemma sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi : sin x = -cos(x + pi/2 + n*(2*pi)) :=
begin
  rw ← cos_eq_cos_add_int_mul_two_pi,
  rw cos_add_pi_div_two,
  rw neg_neg,
end

lemma sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi : sin x = cos(-x + pi/2 + n*(2*pi)) :=
begin
  rw ← cos_eq_cos_add_int_mul_two_pi,
  rw cos_add_pi_div_two,
  rw sin_neg,
  field_simp,
end

lemma cos_eq_sin_add_pi_div_two_add_int_mul_two_pi: cos x = sin(x + pi/2 + n*(2*pi)):=
begin
rw ← sin_eq_sin_add_int_mul_two_pi,
rw sin_add_pi_div_two,
end

lemma cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi: cos x = sin(-x + pi/2 + n*(2*pi)):=
begin
rw ← sin_eq_sin_add_int_mul_two_pi,
rw sin_add_pi_div_two,
rw cos_neg,
end

lemma tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi: tan x = -1 / tan(x + pi/2 + n*pi):=
begin
  rw ← tan_eq_tan_add_int_mul_pi,
  rw tan_eq_sin_div_cos (x+pi/2),
  rw sin_add_pi_div_two,
  rw cos_add_pi_div_two,
  rw tan_eq_sin_div_cos,
  field_simp,
end

lemma tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi: tan x = 1 / tan(-x + pi/2 + n*pi):=
begin
  rw ← tan_eq_tan_add_int_mul_pi,
  rw tan_eq_sin_div_cos (-x+pi/2),
  rw sin_add_pi_div_two,
  rw cos_add_pi_div_two,
  rw tan_eq_sin_div_cos,
  field_simp,
end

lemma sin_eq_sin_neg_add_int_mul_two_pi_add_pi : sin x = sin(-x + n*(2*pi)+pi):=
begin
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi x n,
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi _ 0,
  field_simp,
end

lemma cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi:  cos x = -cos(-x + n*(2*pi) + pi):=
begin
  rw cos_eq_cos_neg_add_int_mul_two_pi x n,
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi _ 0,
  field_simp,
end

lemma sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi : sin x = cos(x + pi/2 + n*(2*pi) + pi):=
begin
  rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi x n,
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi _ 0,
  field_simp,
end

lemma cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi : cos x = -sin(x + pi/2 + n*(2*pi) + pi):=
begin
  rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi x n,
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi _ 0,
  field_simp,
end

lemma sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi : sin x = -cos(-x + pi/2 + n*(2*pi) + pi):=
begin
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi x n,
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi _ 0,
  field_simp,
end

lemma cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi : cos x = -sin(-x + pi/2 + n*(2*pi) + pi):=
begin
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi x n,
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi _ 0,
  field_simp,
end

-- ends here

lemma sin_add_sin : sin x + sin y = 2 * sin((x + y)/2) * cos((x - y)/2):=
begin
  calc sin x + sin y = sin x + sin (- - y) : by tidy
  ... = sin x + - sin (-y) : by rw sin_neg _
  ... = sin x - sin (-y) : by tidy
  ... = 2 * sin ((x - (-y))/2) * cos((x + (-y))/2) : by rw sin_sub_sin x (-y)
  ... = 2 * sin((x + y)/2) * cos((x +  (-y))/2) : by tidy  --ring, norm_num
  ... = 2 * sin((x + y)/2) * cos((x - y)/2) : by tidy, --norm_num, simp, 
end

lemma tan_add (hx:cos x ≠ 0) (hy:cos y≠ 0): tan(x+y) =  (tan x + tan y) / (1 - tan x * tan y):=
begin
  repeat {rw tan_eq_sin_div_cos},
  rw sin_add,
  rw cos_add,
  field_simp,
  ring_exp,
end

lemma tan_two_mul (hx:cos x ≠ 0): tan(2*x) = 2*tan(x)/(1 - tan(x)^2) :=
begin
  have : tan(2*x) = tan(x + x),
  {
    apply congr_arg,
    linarith,
  },
  rw this,
  rw tan_add x x hx hx,
  ring_exp,
end


lemma sq_tan (h: cos x ≠ 0) : 1 + (tan x )^2 = 1 / (cos x)^2:=
begin
    rw tan_eq_sin_div_cos,
    field_simp,
end

lemma sin_to_tan_div_two (h : cos (x/2) ≠ 0): sin x = 2 * tan (x/2) / (1 + tan(x/2)^2):=
begin
  have : sin x = sin (2 * (x/2)),
  apply congr_arg,
  ring,
  rw this,
  rw sin_two_mul,
  have : 1 + tan(x/2)^2 = 1 / cos(x/2)^2,
  {
    rw sq_tan (x/2) h,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  field_simp,
  ring_exp,
end

lemma cos_to_tan_div_two (h: cos (x/2) ≠ 0): cos x =  (1 - tan(x/2)^2)/(1+tan(x/2)^2):=
begin
    have : 1 + tan(x/2)^2 = 1 / cos(x/2)^2,
  {
    rw sq_tan (x/2) h,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  field_simp,
  have : cos x = cos (2*(x/2)),
  {
    apply congr_arg,
    ring,
  },
  rw this,
  rw cos_two_mul',
end

lemma tan_div_two (hx : cos (x/2) ≠ 0): tan(x/2) = (1-cos x) / sin x:=
begin
  rw cos_to_tan_div_two,
  rw sin_to_tan_div_two,
  suffices h:(1+tan(x/2)^2 ≠ 0),
  field_simp,
  have : (tan (x/2) =0) ∨ (tan(x/2)≠ 0),
  {
    finish,
  },
  cases this,
  {
    rw this,
    simp,
  },
  {
    field_simp,
    ring_exp,
  },
  tidy,
  nlinarith,
end

lemma tan_div_two' (hx : cos (x/2) ≠ 0): tan(x/2) = sin x / (1 + cos x):=
begin
  rw cos_to_tan_div_two,
  rw sin_to_tan_div_two,
  suffices h:(1+tan(x/2)^2 ≠ 0),
  field_simp,
  ring,
  tidy,
  nlinarith,
end

lemma tan_sub (hx:cos x ≠ 0) (hy:cos y≠ 0): tan(x-y) =  (tan x - tan y) / (1 + tan x * tan y):=
begin
  have : tan(x-y) = tan(x+ -y),
  ring,
  rw this,
  rw tan_add x (-y),
  rw tan_neg,
  simp,
  ring,
  exact hx,
  rw cos_neg,
  exact hy,
end

lemma tan_add_tan (hx:cos x ≠ 0) (hy:cos y≠ 0) (hz:1-tan x * tan y ≠ 0) : tan x + tan y = tan (x+y) * (1 - tan x * tan y) :=
begin
  rw tan_add _ _ hx hy,
  field_simp,
end

lemma tan_sub_tan (hx:cos x ≠ 0) (hy:cos y≠ 0) (hz:1+tan x * tan y ≠ 0) : tan x - tan y = tan (x-y) * (1 + tan x * tan y) :=
begin
  rw tan_sub _ _ hx hy,
  field_simp,
end

lemma tan_sub_tan' (hx:cos x ≠ 0) (hy:cos y ≠ 0): tan x - tan y = sin (x - y) / (cos x * cos y):=
begin
  repeat {rw tan_eq_sin_div_cos},
  rw sin_sub,
  field_simp,
end

lemma sin_mul_sin : sin x * sin y = cos(x - y) / 2 - cos (x + y) / 2:=
begin
  rw cos_sub,
  rw cos_add,
  ring,
end

lemma sin_mul_cos : sin x * cos y = sin(x - y) / 2  + sin(x + y) / 2:=
begin
  rw sin_sub,
  rw sin_add,
  ring,
end

lemma cos_mul_sin : cos x * sin y = sin(x + y) / 2 - sin(x - y) / 2:=
begin
  rw sin_add,
  rw sin_sub,
  ring,
end

lemma cos_mul_cos : cos x * cos y = cos(x - y) / 2 + cos(x + y) /2 :=
begin
  rw cos_add,
  rw cos_sub,
  ring,
end

lemma tan_mul_tan (hx: cos x ≠ 0) (hy: cos y ≠ 0) (hxy: tan (x-y)≠ 0) (hxy2: 1 +tan x * tan y ≠ 0): tan x * tan y = (tan x - tan y)/tan(x-y) - 1:=
begin
  rw tan_sub_tan,
  field_simp,
  ring,
  tidy,
end

lemma tan_mul_tan' (hx: cos x ≠ 0) (hy: cos y ≠ 0) (hxy: tan (x+y)≠ 0) (hxy2: 1 -tan x * tan y ≠ 0): tan x * tan y = -(tan x + tan y)/tan(x+y) + 1:=
begin
  rw tan_add_tan,
  field_simp,
  ring,
  tidy,
end

--special angles
@[simp] lemma tan_pi: tan π = 0:=
begin
calc tan π = tan (0 + π ) : by simp
     ... = tan 0 : by rw tan_add_pi
     ... = 0 : tan_zero
end

@[simp] lemma tan_pi_div_three : tan (π / 3) = sqrt 3 :=
begin
  rw tan_eq_sin_div_cos _,
  rw sin_pi_div_three,
  rw cos_pi_div_three,
  ring,
end

@[simp] lemma tan_pi_div_six : tan (π / 6) = sqrt 3 / 3:=
begin
  rw tan_eq_sin_div_cos _,
  rw sin_pi_div_six,
  rw cos_pi_div_six,
  field_simp,
end

lemma tan_pi_div_two_sub : tan (π / 2 - x) = 1 / tan x :=
begin
  repeat {rw tan_eq_sin_div_cos},
  rw sin_pi_div_two_sub,
  rw cos_pi_div_two_sub,
  field_simp,
end

lemma sin_two_pi_div_three : sin (2*pi/3) = sqrt 3 / 2:=
begin
  have : sin (2*pi/3) = sin(pi/3),
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi _ 0,
  apply congr_arg _,
  simp,
  ring,
  rw this,
  rw sin_pi_div_three,
end

lemma sin_three_pi_div_four : sin(3*pi/4) = sqrt 2/2:=
begin
  have :sin(3*pi/4) = sin(pi/4),
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi _ 0,
  apply congr_arg _,
  simp,
  ring,
  rw this,
  rw sin_pi_div_four,
end

lemma sin_five_pi_div_six : sin(5*pi/6) = 1/2:=
begin
  have :sin(5*pi/6)  = sin(pi/6),
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi _ 0,
  apply congr_arg _,
  simp,
  ring,
  rw this,
  rw sin_pi_div_six,
end

lemma cos_two_pi_div_three : cos (2*pi/3) = - 1 / 2:=
begin
  have : cos (2*pi/3) = -cos(pi/3),
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi _ 0,
  repeat {apply congr_arg _},
  simp,
  ring,
  rw this,
  rw cos_pi_div_three,
  ring,
end

lemma cos_three_pi_div_four : cos (3*pi/4) = - sqrt 2 / 2:=
begin
  have : cos (3*pi/4) = -cos(pi/4),
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi _ 0,
  repeat {apply congr_arg _},
  simp,
  ring,
  rw this,
  rw cos_pi_div_four,
  ring,
end

lemma cos_five_pi_div_six : cos (5*pi/6) = - sqrt 3 / 2:=
begin
  have : cos (5*pi/6) = -cos(pi/6),
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi _ 0,
  repeat {apply congr_arg _},
  simp,
  ring,
  rw this,
  rw cos_pi_div_six,
  ring,
end

lemma tan_two_pi_div_three : tan (2*pi/3) = - sqrt 3:=
begin
  have : tan (2*pi/3) = -tan(pi/3),
  rw tan_eq_neg_tan_neg_add_int_mul_pi _ 1,
  repeat {apply congr_arg _},
  simp,
  ring,
  rw this,
  rw tan_pi_div_three,
end

lemma tan_three_pi_div_four : tan (3*pi/4) = - 1:=
begin
  have : tan (3*pi/4) = -tan(pi/4),
  rw tan_eq_neg_tan_neg_add_int_mul_pi _ 1,
  repeat {apply congr_arg _},
  simp,
  ring,
  rw this,
  rw tan_pi_div_four,
end

lemma tan_five_pi_div_six : tan (5*pi/6) = - sqrt 3 / 3:=
begin
  have : tan (5*pi/6) = -tan(pi/6),
  rw tan_eq_neg_tan_neg_add_int_mul_pi _ 1,
  repeat {apply congr_arg _},
  simp,
  ring,
  rw this,
  rw tan_pi_div_six,
  ring,
end

lemma sin_pi_div_twelve: sin(pi/12) = -sqrt(2)/4 + sqrt(6)/4 :=
begin
  have : sin(pi/12) = sin(pi/4-pi/6),
  apply congr_arg,
  ring,
  rw this,
  rw sin_sub,
  field_simp,
  rw ← sqrt_mul,
  norm_num,
  tidy,
  ring,
end

lemma cos_pi_div_twelve: cos(pi/12) = sqrt(2)/4 + sqrt(6)/4 :=
begin
  have : cos(pi/12) = cos(pi/4-pi/6),
  apply congr_arg,
  ring,
  rw this,
  rw cos_sub,
  field_simp,
  rw ← sqrt_mul,
  norm_num,
  tidy,
  ring,
end

lemma tan_pi_div_twelve: tan(pi/12) = 2 - sqrt 3 :=
begin
  have : tan(pi/12) = tan(pi/4-pi/6),
  apply congr_arg,
  ring,
  rw this,
  rw tan_sub,
  field_simp,
  suffices : 3 + sqrt 3 ≠ 0,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  tidy,
  have : sqrt 3 ≥ 0,
  apply sqrt_nonneg,
  linarith,
  let := sqrt_eq_zero'.1 ᾰ,
  linarith,
end

--special angles ends

lemma cos_two_mul'' : cos (2 * x) = 1 - 2 * sin x ^ 2 :=
begin
  rw cos_two_mul,
  rw cos_sq',
  ring,
end

