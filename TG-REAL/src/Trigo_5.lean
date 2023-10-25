import trigo_import
open real
open_locale real
variables (x y : ℝ)

lemma Trigo_3_250_NCWT (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(-x)/tan(x + pi) + cos(x - pi)*cos(x + pi/2)/sin(x + 5*pi/2)=sin(x)-cos(x):=
begin
  have : tan(x + pi) = tan(x),
  {
  rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(-x) = -sin(x),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  have : cos(x - pi) = -cos(x),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x - pi) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(x + pi/2) = -sin(x),
  {
  rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(x + 5*pi/2) = cos(x),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + 5*pi/2) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_3_251_ZNDS : sin(pi/12)**2 + sqrt(3)*sin(pi/12)*cos(pi/12)=1/2:=
begin
  rw sin_pi_div_twelve,
  rw cos_pi_div_twelve,
  ring_exp,
  repeat {rw sq_sqrt},
  ring,
  rw mul_assoc,
  rw ← sqrt_mul,
  have : sqrt(6*2) = sqrt(3*4),
  {
    apply congr_arg,
    ring,
  },
  rw this,
  rw sqrt_mul,
  have : sqrt(4) = sqrt(2**2),
  {
    apply congr_arg,
    ring,
  },
  rw this,
  rw sqrt_sq,
  ring,
  repeat {linarith},
end

lemma Trigo_3_252_UKFL (h0 : sin(pi/12) ≠ 0) (h1 : cos(pi/12) ≠ 0) : -(2*sin(pi/24)**2 - 1)/(sin(pi/24)*cos(pi/24)) + 2*tan(pi/12)=8:=
begin
  have : sin(pi/24)*cos(pi/24) = sin(pi/12)/2,
  {
  have : sin(pi/12) = 2*sin(pi/24)*cos(pi/24),
  {
  have : sin (pi/12) = sin(2*(pi/24)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  have : 2*sin(pi/24)**2 = 1 - cos(pi/12),
  {
  have : sin(pi/24)**2 = 1/2 - cos(pi/12)/2,
  {
  have : cos (pi/12) = cos(2*(pi/24)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  linarith,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  have : -(1-cos(pi/12) - 1)/(sin(pi/12)/2) + 2*(sin(pi/12)/cos(pi/12)) = 2*sin(pi/12)/cos(pi/12) + 2*cos(pi/12)/sin(pi/12),
  {
    field_simp,
    ring,
  },
  rw this,
  have : 2*sin(pi/12)/cos(pi/12) + 2*cos(pi/12)/sin(pi/12) = (2*sin(pi/12)**2 + 2*cos(pi/12)**2)/(sin(pi/12)*cos(pi/12)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : 2*sin(pi/12)**2 + 2*cos(pi/12)**2 = 2,
  {
  have : sin(pi/12)**2 + cos(pi/12)**2 = 1,
  {
  rw sin_sq_add_cos_sq,
  },
  linarith,
  },
  rw this,
  have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
  {
  have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
  {
  have : sin (pi/6) = sin(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_3_253_IKHE (h0 : 6 - sqrt(3) ≠ 0) : (3 - sin(pi/3))/(2 - cos(pi/12)**2)=2:=
begin
  have : cos(pi/12)**2 = cos(pi/6)/2 + 1/2,
  {
  have : cos (pi/6) = cos(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  rw cos_pi_div_six,
  rw sin_pi_div_three,
  have : 2 - (sqrt(3)/2/2 + 1/2) = (6 - sqrt(3))/4,
  {
    ring,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_3_254_JFVI : sin(-x + pi/10)*cos(x + 3*pi/20) + sin(x + 3*pi/20)*cos(-x + pi/10)=sqrt(2)/2:=
begin
  have : sin(-x + pi/10)*cos(x + 3*pi/20) + sin(x + 3*pi/20)*cos(-x + pi/10) = sin(pi/4),
  {
  have : sin(pi/4) = sin((x + 3*pi/20) + (-x + pi/10)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add (x + 3*pi/20) (-x + pi/10),
  ring,
  },
  rw this,
  rw sin_pi_div_four,
end

lemma Trigo_3_255_PNBN (h0 : sqrt(3) ≠ 0) : cos(-19*pi/3)*cos(-19*pi/6)*tan(-5*pi/6)/(sin(-23*pi/6)*tan(-7*pi/6))=sqrt(3)/2:=
begin
  have : cos(-19*pi/3) = cos(pi/3),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-19*pi/3) (-3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  have : cos(-19*pi/6) = -cos(pi/6),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-19*pi/6) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  have : tan(-5*pi/6) = -tan(5*pi/6),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-5*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(5*pi/6) = -tan(pi/6),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (5*pi/6) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_six,
  have : sin(-23*pi/6) = -sin(23*pi/6),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-23*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(23*pi/6) = -sin(pi/6),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (23*pi/6) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  have : tan(-7*pi/6) = -tan(pi/6),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-7*pi/6) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_3_256_JROG (h0 : -sin(pi/8) + cos(pi/8) ≥ 0) (h1 : sin(pi/8) + cos(pi/8) ≥ 0) (h3 : sin(pi/8) + cos(pi/8) ≠ 0) : sqrt((1 - sin(pi/4))/(sin(pi/4) + 1))*cos(pi/4) =1-sqrt(2)/2:=
begin
  have : 1 - sin(pi/4) = sin(pi/8)**2 + cos(pi/8)**2 - sin(pi/4),
  {
    rw sin_sq_add_cos_sq,
  },
  rw this,
  have :  sin(pi/4) + 1 = sin(pi/4) + sin(pi/8)**2 + cos(pi/8)**2,
  {
    rw add_assoc,
    rw sin_sq_add_cos_sq,
  },
  rw this,
  have : sin(pi/4) = 2*sin(pi/8)*cos(pi/8),
  {
  have : sin (pi/4) = sin(2*(pi/8)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  repeat {rw this},
  have :sin(pi/8)**2 + cos(pi/8)**2 - 2*sin(pi/8)*cos(pi/8)  = (-sin(pi/8) + cos(pi/8))**2,
  {
  ring_exp,
  },
  rw this,
  have : 2*sin(pi/8)*cos(pi/8) + sin(pi/8)**2 + cos(pi/8)**2 = (sin(pi/8) + cos(pi/8))**2,
  {
  ring_exp,
  },
  rw this,
  rw sqrt_div,
  repeat {rw sqrt_sq_eq_abs},
  rw abs_eq_self.mpr h1,
  rw abs_eq_self.mpr h0,
    have : cos(pi/4) = -sin(pi/8)**2 + cos(pi/8)**2,
  {
  have : cos (pi/4) = cos(2*(pi/8)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,  
  have : -sin(pi/8)**2 + cos(pi/8)**2 = (-sin(pi/8) + cos(pi/8))*(sin(pi/8) + cos(pi/8)),
  {
  ring_exp,
  },
  rw this,
  have : (-sin(pi/8) + cos(pi/8))/(sin(pi/8) + cos(pi/8))*((-sin(pi/8) + cos(pi/8))*(sin(pi/8) + cos(pi/8))) =  (-sin(pi/8) + cos(pi/8))**2,
  {
    field_simp [-sin_pi_div_eight, -cos_pi_div_eight],
    ring_exp,
  },
  rw this,
  ring_exp,
  rw sin_sq_add_cos_sq,
  rw ← mul_assoc,
  have : sin(pi/8)*cos(pi/8) = sin(pi/4)/2,
  {
  have : sin(pi/4) = 2*sin(pi/8)*cos(pi/8),
  {
  have : sin (pi/4) = sin(2*(pi/8)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  rw sin_pi_div_four,
  ring,
  repeat{linarith},
  apply sq_nonneg,
end

lemma Trigo_3_257_CCUC : sin(47*pi/180)*cos(17*pi/180) - cos(47*pi/180)*cos(73*pi/180)=1/2:=
begin
  have : cos(73*pi/180) = sin(17*pi/180),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (73*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sub_eq_neg_add,
  rw mul_comm,
  rw ← neg_mul,
  have : -sin(17*pi/180)*cos(47*pi/180) + sin(47*pi/180)*cos(17*pi/180) = sin(pi/6),
  {
  have : sin(pi/6) = sin((47*pi/180) - (17*pi/180)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  rw sin_pi_div_six,
end

lemma Trigo_3_258_LGVG (h0 : sin(pi/18) ≠ 0) (h1 : sqrt(3) ≠ 0) : (cos(pi/9) - cos(2*pi/9))/(sin(pi/9) - sin(2*pi/9))=-sqrt(3)/3:=
begin
  rw sub_eq_neg_add,
  have : -cos(2*pi/9) + cos(pi/9) = -2*sin(-pi/18)*sin(pi/6),
  {
  rw neg_add_eq_sub,
  rw cos_sub_cos,
  have : sin(((pi/9) + (2*pi/9))/2) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((pi/9) - (2*pi/9))/2) = sin(-pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw sin_pi_div_six,
  have : sin(-pi/18) = -sin(pi/18),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sub_eq_neg_add,
  have : -sin(2*pi/9) + sin(pi/9) = 2*sin(-pi/18)*cos(pi/6),
  {
  rw neg_add_eq_sub,
  rw sin_sub_sin,
  have : cos(((pi/9) + (2*pi/9))/2) = cos (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((pi/9) - (2*pi/9))/2) = sin(-pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  have : sin(-pi/18) = -sin(pi/18),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_3_259_RLOJ (h0 : sin(x) ≠ 0) : sin(x + pi)*cos(-x + 2*pi)/cos(x + pi/2)=cos(x):=
begin
  have : sin(x + pi) = -sin(x),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-x + 2*pi) = cos(x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(x + pi/2) = -sin(x),
  {
  rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  rw div_neg,
  field_simp,
  ring_exp,
end

lemma Trigo_3_260_LPTS (h0 : sin(pi/36) ≠ 0) (h1 : cos(pi/36) ≠ 0) (h2 : sin(pi/18) ≠ 0) (h3 : sin(pi/9) ≠ 0) : (1 - cos(pi/9))*(-tan(pi/36) + 1/tan(pi/36))/(sqrt(3)*sin(5*pi/18) - cos(5*pi/18))=1:=
begin
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  rw ← neg_div,
  have : -sin(pi/36)/cos(pi/36) + cos(pi/36)/sin(pi/36) = (-sin(pi/36)**2 + cos(pi/36)**2)/(sin(pi/36)*cos(pi/36)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_three, -cos_pi_div_three],
  ring_exp,
  },
  rw this,
  have : -sin(pi/36)**2 + cos(pi/36)**2 = cos(pi/18),
  {
  have : cos (pi/18) = cos(2*(pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : sin(pi/36)*cos(pi/36) = sin(pi/18)/2,
  {
  have : sin(pi/18) = 2*sin(pi/36)*cos(pi/36),
  {
  have : sin (pi/18) = sin(2*(pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  have : cos(5*pi/18) = 2*sin(pi/6)*cos(5*pi/18),
  {
  field_simp,
  },
  rw this,
  have : sqrt(3)*sin(5*pi/18) = 2*sin(5*pi/18)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  rw sub_eq_neg_add (2*sin(5*pi/18)*cos(pi/6)) (2*sin(pi/6)*cos(5*pi/18)),
  rw ← neg_mul,
  rw ← neg_mul,
  have : -2*sin(pi/6)*cos(5*pi/18) + 2*sin(5*pi/18)*cos(pi/6) = 2*sin(pi/9),
  {
  have : sin(pi/9) = -sin(pi/6)*cos(5*pi/18) + sin(5*pi/18)*cos(pi/6),
  {
  have : sin(pi/9) = sin((5*pi/18) - (pi/6)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  linarith,
  },
  rw this,
  have : 1 - cos(pi/9) = 2*sin(pi/18)**2,
  {
  have : cos (pi/9) = cos(2*(pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : 2*sin(pi/18)**2*(cos(pi/18)/(sin(pi/18)/2))/(2*sin(pi/9)) = 2*sin(pi/18)*cos(pi/18)/sin(pi/9),
  {
    field_simp,
    ring_exp,
  },
  rw this,
  have : 2*sin(pi/18)*cos(pi/18) = sin(pi/9),
  {
  have : sin (pi/9) = sin(2*(pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  field_simp,
end

lemma Trigo_3_261_OXAZ (h0 : sin(pi/12) ≠ 0) (h1 : cos(pi/12) ≠ 0) : tan(pi/12) - 1/tan(pi/12)=-2*sqrt(3):=
begin
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  have : sin(pi/12)/cos(pi/12) - cos(pi/12)/sin(pi/12) = (-cos(pi/12)**2 + sin(pi/12)**2)/(sin(pi/12)*cos(pi/12)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : -cos(pi/12)**2 + sin(pi/12)**2 = -cos(pi/6),
  {
  have : cos(pi/6) = -sin(pi/12)**2 + cos(pi/12)**2,
  {
  have : cos (pi/6) = cos(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  linarith,
  },
  rw this,
  have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
  {
  have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
  {
  have : sin (pi/6) = sin(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  rw cos_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_3_262_LLVY : sin(163*pi/180)*sin(223*pi/180) + sin(253*pi/180)*sin(313*pi/180)=1/2:=
begin
  have : sin(163*pi/180) = sin(17*pi/180),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (163*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(223*pi/180) = -cos(47*pi/180),
  {
  rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (223*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(253*pi/180) = -cos(17*pi/180),
  {
  rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (253*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(313*pi/180) = -sin(47*pi/180),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (313*pi/180) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  repeat {rw mul_neg},
  repeat {rw ← neg_mul},
  rw neg_neg,
  rw mul_comm (cos(17*pi/180)) (sin(47*pi/180)),
  have : -sin(17*pi/180)*cos(47*pi/180) + sin(47*pi/180)*cos(17*pi/180) = sin(pi/6),
  {
  have : sin(pi/6) = sin((47*pi/180) - (17*pi/180)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  rw sin_pi_div_six,
end

lemma Trigo_3_263_NSHA (h0 : cos(4*pi/9) ≥ 0) : sqrt(1 - sin(4*pi/9)**2)=cos(4*pi/9):=
begin
  have : 1 - sin(4*pi/9)**2 = cos(4*pi/9)**2,
  {
  rw cos_sq',
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h0,
end

lemma Trigo_3_264_LRYC (h0 : sin(pi/18) - cos(pi/18) ≠ 0) (h1 : -sin(pi/18) + cos(pi/18) ≥ 0) (h2 : sin(pi/18) ≥ 0) : sqrt(-2*sin(pi/18)*cos(pi/18) + 1)/(sqrt(1 - cos(17*pi/18)**2) - cos(37*pi/18))=-1:=
begin
  have : cos(37*pi/18) = cos(pi/18),
  {
  rw cos_eq_cos_add_int_mul_two_pi (37*pi/18) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(17*pi/18) = -cos(pi/18),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : -2*sin(pi/18)*cos(pi/18) + 1 = -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2 ,
  {
    rw add_assoc,
    rw sin_sq_add_cos_sq,
  },
  rw this,
  have : -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2 = (-sin(pi/18) + cos(pi/18))**2,
  {
  ring_exp,
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h1,
  rw neg_sq,
  rw ← sin_sq,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h2,
  field_simp,
  ring_exp,
end

lemma Trigo_3_265_MHKB (h0 : 2 ≠ 0) (h1 : 4 ≠ 0) : sin(x)**2 + sin(x + pi/3)**2 + sin(x + 2*pi/3)**2=3/2:=
begin
  have : sin(x + pi/3) = sin(x)*cos(pi/3) + sin(pi/3)*cos(x),
  {
  have : sin(x+pi/3) = sin((x) + (pi/3)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_add,
  ring,
  },
  rw this,
  have : sin(x + 2*pi/3) = sin(x)*cos(2*pi/3) + sin(2*pi/3)*cos(x),
  {
  have : sin(x+2*pi/3) = sin((x) + (2*pi/3)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_add,
  ring,
  },
  rw this,
  have : cos(2*pi/3) = -cos(pi/3),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(2*pi/3) = sin(pi/3),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  have : (sin(x)*-(1/2) + sqrt(3)/2*cos(x))**2 = sin(x)**2/4 - sqrt(3)*sin(x)*cos(x)/2 + 3*cos(x)**2/4,
  {
  ring_exp,
  rw sq_sqrt,
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  linarith,
  },
  rw this,
  have : (sin(x)*(1/2) + sqrt(3)/2*cos(x))**2 = sin(x)**2/4 + sqrt(3)*sin(x)*cos(x)/2 + 3*cos(x)**2/4,
  {
  ring_exp,
  rw sq_sqrt,
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  linarith,
  },
  rw this,
  ring_exp,
  have : sin(x)**2*(3/2) + cos(x)**2*(3/2) = 3/2,
  {
  have : sin(x)**2 + cos(x)**2 = 1,
  {
  rw sin_sq_add_cos_sq,
  },
  linarith,
  },
  rw this,
end

lemma Trigo_3_266_BEXW (h0 : sin(pi/9) ≠ 0) : sin(pi/18)*sin(pi/6)*cos(pi/9)*cos(2*pi/9)=1/16:=
begin
  have : sin(pi/6) = cos(pi/3),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(pi/18) = cos(4*pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(pi/9) = sin(2*pi/9)/(2*sin(pi/9)),
  {
  have : sin (2*pi/9) = sin(2*(pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  field_simp,
  ring,
  },
  rw this,
  have : cos(4*pi/9)*cos(pi/3)*(sin(2*pi/9)/(2*sin(pi/9)))*cos(2*pi/9) = cos(4*pi/9)*cos(pi/3)*(sin(2*pi/9)*cos(2*pi/9)/(2*sin(pi/9))),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9)/2,
  {
  have : sin(4*pi/9) = 2*sin(2*pi/9)*cos(2*pi/9),
  {
  have : sin (4*pi/9) = sin(2*(2*pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  have : cos(4*pi/9)*cos(pi/3)*(sin(4*pi/9)/2/(2*sin(pi/9))) = sin(4*pi/9)*cos(4*pi/9)*cos(pi/3)/2/(2*sin(pi/9)),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : sin(4*pi/9)*cos(4*pi/9) = sin(8*pi/9)/2,
  {
  have : sin(8*pi/9) = 2*sin(4*pi/9)*cos(4*pi/9),
  {
  have : sin (8*pi/9) = sin(2*(4*pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  have : sin(8*pi/9) = sin(pi/9),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  field_simp,
  ring_exp,
end

lemma Trigo_3_267_WSKL : sin(pi/12)**4 - cos(pi/12)**4=-sqrt(3)/2:=
begin
  have : sin(pi/12)**4 - cos(pi/12)**4 = (sin(pi/12)**2 - cos(pi/12)**2)*(sin(pi/12)**2 + cos(pi/12)**2),
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  have : sin(pi/12)**2 - cos(pi/12)**2 = -cos(pi/6),
  {
  have : cos(pi/6) = -sin(pi/12)**2 + cos(pi/12)**2,
  {
  have : cos(pi/6) = cos(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw cos_pi_div_six,
  ring,
end

lemma Trigo_3_268_TAEG (h0 : cos(2*pi/45) ≠ 0) (h1 : cos(pi/12) ≠ 0) : (sin(7*pi/180) + sin(2*pi/45)*cos(pi/12))/(-sin(2*pi/45)*sin(pi/12) + cos(7*pi/180))=2-sqrt(3):=
begin
  have : sin(2*pi/45)*cos(pi/12) = sin(-7*pi/180)/2 + sin(23*pi/180)/2,
  {
  rw sin_mul_cos,
  have : sin((2*pi/45) + (pi/12)) = sin (23*pi/180),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((2*pi/45) - (pi/12)) = sin (-7*pi/180),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  have : sin(-7*pi/180) = -sin(7*pi/180),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-7*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw neg_mul,
  have : sin(2*pi/45)*sin(pi/12) = -cos(23*pi/180)/2 + cos(-7*pi/180)/2,
  {
  rw sin_mul_sin,
  have : cos((2*pi/45) + (pi/12)) = cos (23*pi/180),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((2*pi/45) - (pi/12)) = cos (-7*pi/180),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : cos(-7*pi/180) = cos(7*pi/180),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-7*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(7*pi/180) + (-sin(7*pi/180)/2 + sin(23*pi/180)/2) = sin(7*pi/180)/2 + sin(23*pi/180)/2,
  {
  ring,
  },
  rw this,
  have : sin(7*pi/180)/2 + sin(23*pi/180)/2 = sin(pi/12)*cos(2*pi/45),
  {
  have : sin(7*pi/180) + sin(23*pi/180) = 2*sin(pi/12)*cos(2*pi/45),
  {
  rw add_comm,
  rw sin_add_sin,
  have : sin(((23*pi/180) + (7*pi/180))/2) = sin (pi/12),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos(((23*pi/180) - (7*pi/180))/2) = cos(2*pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  have : -(-cos(23*pi/180)/2 + cos(7*pi/180)/2) + cos(7*pi/180) = cos(23*pi/180)/2 + cos(7*pi/180)/2,
  {
  ring,
  },
  rw this,
  have : cos(23*pi/180)/2 + cos(7*pi/180)/2 = cos(2*pi/45)*cos(pi/12),
  {
  have : cos(7*pi/180) + cos(23*pi/180) = 2*cos(2*pi/45)*cos(pi/12),
  {
  rw add_comm,
  rw cos_add_cos,
  have : cos(((23*pi/180) + (7*pi/180))/2) = cos (pi/12),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos(((23*pi/180) - (7*pi/180))/2) = cos(2*pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  linarith,
  },
  rw this,
  have : sin(pi/12)*cos(2*pi/45)/(cos(2*pi/45)*cos(pi/12)) = sin(pi/12)/cos(pi/12),
  {
  field_simp,
  ring,
  },
  rw this,
  rw ← tan_eq_sin_div_cos,
  rw tan_pi_div_twelve,
end

lemma Trigo_3_269_GGMF (h0 : cos(x/2) ≠ 0) (h1 : sin(x/2) ≠ 0) (h2 : sin(x) ≠ 0) : (-tan(x/2) + 1/tan(x/2))*sin(2*x)=4*cos(x)**2:=
begin
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  have : -(sin(x/2)/cos(x/2)) + cos(x/2)/sin(x/2) = (-sin(x/2)**2 + cos(x/2)**2)/(sin(x/2)*cos(x/2)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : -sin(x/2)**2 + cos(x/2)**2 = cos(x),
  {
  have : cos (x) = cos(2*(x/2)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : sin(x/2)*cos(x/2) = sin(x)/2,
  {
  have : sin(x) = 2*sin(x/2)*cos(x/2),
  {
  have : sin (x) = sin(2*(x/2)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  have : sin(2*x) = 2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_3_270_MUCD (h0 : cos(11*pi/60) ≠ 0) (h1 : cos(3*pi/20) ≠ 0) : (-tan(3*pi/20)*tan(11*pi/60) + 1)/(tan(3*pi/20) + tan(11*pi/60))=sqrt(3)/3:=
begin
  rw ← one_div_div,
  have : (tan(3*pi/20) + tan(11*pi/60))/(-tan(3*pi/20)*tan(11*pi/60) + 1) = tan(pi/3),
  {
  have : tan(pi/3) = tan((3*pi/20) + (11*pi/60)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw tan_add,
  field_simp,
  ring_exp,
  repeat {assumption},
  },
  rw this,
  rw tan_pi_div_three,
  field_simp,
end

lemma Trigo_3_271_VDDH (h0 : sin(pi/12) ≠ 0) (h1 : cos(pi/12) ≠ 0) : -tan(pi/12) + 1/tan(pi/12)=2*sqrt(3):=
begin
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  rw ← neg_div,
  have : -sin(pi/12)/cos(pi/12) + cos(pi/12)/sin(pi/12) = (-sin(pi/12)**2 + cos(pi/12)**2)/(sin(pi/12)*cos(pi/12)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : -sin(pi/12)**2 + cos(pi/12)**2 = cos(pi/6),
  {
  have : cos (pi/6) = cos(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
  {
  have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
  {
  have : sin (pi/6) = sin(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  rw sin_pi_div_six,
  field_simp,
  ring_exp,
end

lemma Trigo_3_272_IFMC (h0 : 2 - sqrt(3) ≠ 0) : tan(7*pi/12)=-2-sqrt(3):=
begin
  have : tan(7*pi/12) = -1/tan(pi/12),
  {
  rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (7*pi/12) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_twelve,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_3_273_HDTY (h0 : cos(x) ≠ 0) : (sin(x + pi/6) + cos(x + pi/3))/cos(x)=1:=
begin
  have : sin(x + pi/6) = sin(x)*cos(pi/6) + sin(pi/6)*cos(x),
  {
  have : sin(x+pi/6) = sin((x) + (pi/6)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_add,
  ring,
  },
  rw this,
  have : cos(x + pi/3) = -sin(pi/3)*sin(x) + cos(pi/3)*cos(x),
  {
  have : cos(x+pi/3) = cos((x) + (pi/3)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_add,
  ring,
  },
  rw this,
  rw sin_pi_div_six,
  rw sin_pi_div_three,
  rw cos_pi_div_six,
  rw cos_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_3_274_GJQO : (-sin(pi/12) + sin(5*pi/12))*(cos(pi/12) + cos(5*pi/12))=sqrt(3)/2:=
begin
  have : -sin(pi/12) + sin(5*pi/12) = 2*sin(pi/6)*cos(pi/4),
  {
  rw neg_add_eq_sub,
  rw sin_sub_sin,
  have : cos(((5*pi/12) + (pi/12))/2) = cos (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((5*pi/12) - (pi/12))/2) = sin(pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  rw add_comm,
  have : cos(5*pi/12) + cos(pi/12) = 2*cos(pi/6)*cos(pi/4),
  {
  rw cos_add_cos,
  have : cos(((5*pi/12) + (pi/12))/2) = cos (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos(((5*pi/12) - (pi/12))/2) = cos(pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw sin_pi_div_six,
  rw cos_pi_div_six,
  rw cos_pi_div_four,
  norm_num,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_3_275_SIQT : (cos(2*x) + 1)*sin(x)=sin(2*x)*cos(x):=
begin
  have : cos(2*x) = -sin(x)**2 + cos(x)**2,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_two_mul',
  ring,
  },
  rw this,
  rw sin_sq,
  have : sin(2*x) = 2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  norm_num,
  ring_exp,
end

lemma Trigo_3_276_BTCL (h0 : -cos(pi/18) + sin(pi/18) ≠ 0) (h1 : cos(pi/18) ≥ 0) (h2 : -cos(pi/18) + sin(pi/18) ≤ 0) : sqrt(-2*sin(pi/18)*cos(pi/18) + 1)/(-sqrt(1 - sin(17*pi/18)**2) + sin(17*pi/18))=-1:=
begin
  have : sin(17*pi/18) = sin(pi/18),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw ← cos_sq',
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h1,
  have : -2*sin(pi/18)*cos(pi/18)+1 = -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2,
  {
  rw add_assoc,
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2 = (-cos(pi/18) + sin(pi/18))**2,
  {
  ring_exp,
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_neg_self.mpr h2,
  norm_num,
  field_simp,
end

lemma Trigo_3_277_LWCL : 4*sin(7*pi/12)*cos(pi/12)=2+sqrt(3):=
begin
  rw mul_assoc,
  have : sin(7*pi/12)*cos(pi/12) = sin(2*pi/3)/2 + sin(pi/2)/2,
  {
  rw sin_mul_cos,
  have : sin((7*pi/12) + (pi/12)) = sin (2*pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((7*pi/12) - (pi/12)) = sin (pi/2),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw sin_two_pi_div_three,
  rw sin_pi_div_two,
  ring_exp,
end

lemma Trigo_3_278_QZBL : (sin(pi/8) - cos(pi/8))*(sin(pi/8) + cos(pi/8))=-sqrt(2)/2:=
begin
  have : (sin(pi/8) - cos(pi/8))*(sin(pi/8) + cos(pi/8)) = -cos(pi/8)**2 + sin(pi/8)**2,
  {
  ring_exp,
  },
  rw this,
  have : -cos(pi/8)**2 + sin(pi/8)**2 = -cos(pi/4),
  {
  have : cos(pi/4) = -sin(pi/8)**2 + cos(pi/8)**2,
  {
  have : cos (pi/4) = cos(2*(pi/8)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  linarith,
  },
  rw this,
  rw cos_pi_div_four,
  ring,
end

lemma Trigo_3_279_WUKR (h0 : cos(4) ≤ 0) (h1 : sin(4) - cos(4) ≤ 0) : 2*sqrt(1 - sin(8)) + sqrt(2*cos(8) + 2)=-2*sin(4):=
begin
  have : sin(8) = 2*sin(4)*cos(4),
  {
  have : sin (8) = sin(2*(4)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : 1 - 2*sin(4)*cos(4) = cos(4)**2 + sin(4)**2 - 2*sin(4)*cos(4),
  {
  rw cos_sq_add_sin_sq,
  },
  rw this,
  have : cos(4)**2 + sin(4)**2 - 2*sin(4)*cos(4) = (sin(4) - cos(4))**2,
  {
  ring_exp,
  },
  rw this,
  have : 2 * cos(8) + 2 = 4*cos(4)**2,
  {
  have : cos(8) + 1 = 2*cos(4)**2,
  {
  have : cos(8) = cos(2*4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  linarith,
  },
  rw this,
  rw sqrt_mul,
  repeat {rw sqrt_sq_eq_abs},
  rw abs_eq_neg_self.mpr h0,
  rw abs_eq_neg_self.mpr h1,
  have : sqrt(4) = sqrt(2**2),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sqrt_sq,
  ring,
  repeat {linarith},
end

lemma Trigo_3_280_KWKF (h0 : sin(pi/8) ≠ 0) (h1 : cos(pi/8) ≠ 0) : -tan(pi/8) + tan(3*pi/8)=2:=
begin
  have : tan(3*pi/8) = 1/tan(pi/8),
  {
  rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (3*pi/8) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  rw ← neg_div,
  have : -sin(pi/8)/cos(pi/8) + cos(pi/8)/sin(pi/8) = (-sin(pi/8)**2 + cos(pi/8)**2)/(sin(pi/8)*cos(pi/8)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_eight, -cos_pi_div_eight],
  ring_exp,
  },
  rw this,
  have : -sin(pi/8)**2 + cos(pi/8)**2 = cos(pi/4),
  {
  have : cos (pi/4) = cos(2*(pi/8)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : sin(pi/8)*cos(pi/8) = sin(pi/4)/2,
  {
  have : sin(pi/4) = 2*sin(pi/8)*cos(pi/8),
  {
  have : sin (pi/4) = sin(2*(pi/8)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  rw cos_pi_div_four,
  rw sin_pi_div_four,
  field_simp,
  ring_exp,
end

lemma Trigo_3_281_ORXD : 2*cos(pi/12)**2 - 1=sqrt(3)/2:=
begin
  have : 2*cos(pi/12)**2 = cos(pi/6) + 1,
  {
  have : cos(pi/6) = cos(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  rw cos_pi_div_six,
  ring_exp,
end

lemma Trigo_3_282_UJUW (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(-x - 2*pi)*cos(-x + 6*pi)*tan(-x + 2*pi)/(sin(x + 5*pi)*cos(x - pi))=tan(x):=
begin
  have : sin(-x - 2*pi) = -sin(x),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x - 2*pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-x + 6*pi) = cos(x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 6*pi) (3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(-x + 2*pi) = -tan(x),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-x + 2*pi) (2),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(x + 5*pi) = -sin(x),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + 5*pi) (-3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(x - pi) = cos(pi - x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (x - pi) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(pi - x) = -cos(x),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_3_283_GBSP : sin(29*pi/180)*sin(91*pi/180) - sin(119*pi/180)*sin(181*pi/180)=1/2:=
begin
  rw sub_eq_neg_add,
  rw ← neg_mul,
  have : -sin(119*pi/180)*sin(181*pi/180) = -cos(31*pi/90)/2 + cos(5*pi/3)/2,
  {
  have : sin(119*pi/180)*sin(181*pi/180) = cos(31*pi/90)/2 - cos(5*pi/3)/2,
  {
  rw mul_comm,
  rw sin_mul_sin,
  have : cos((181*pi/180) + (119*pi/180)) = cos (5*pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((181*pi/180) - (119*pi/180)) = cos (31*pi/90),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  have : sin(29*pi/180)*sin(91*pi/180) = cos(31*pi/90)/2 - cos(2*pi/3)/2,
  {
  rw mul_comm,
  rw sin_mul_sin,
  have : cos((91*pi/180) + (29*pi/180)) = cos (2*pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((91*pi/180) - (29*pi/180)) = cos (31*pi/90),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  have : cos(5*pi/3) = cos(pi/3),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (5*pi/3) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(2*pi/3) = -cos(pi/3),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_3_284_OVUD (h0 : 2 ≠ 0) (h1 : sin(x) + cos(x) ≠ 0) (h2 : cos(x) ≠ 0) : (sin(2*x) + 1)/(sin(2*x) + cos(2*x) + 1)=1/2*tan(x)+1/2:=
begin
  have : sin(2*x) = 2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_two_mul,
  },
  rw this,
  have : 2*sin(x)*cos(x) + 1 = 2*sin(x)*cos(x) + sin(x)**2 + cos(x)**2,
  {
  rw add_assoc,
  rw sin_sq_add_cos_sq,
  },
  rw this,
  rw add_assoc (2*sin(x)*cos(x)) (cos(2*x)) 1,
  have : cos(2*x) + 1 = 2*cos(x)**2,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  have : 2*sin(x)*cos(x) + sin(x)**2 + cos(x)**2 = (sin(x) + cos(x))**2,
  {
  ring_exp,
  },
  rw this,
  have : 2*sin(x)*cos(x) + 2*cos(x)**2 = 2*(sin(x) + cos(x))*cos(x),
  {
  ring_exp,
  },
  rw this,
  have : (sin(x) + cos(x))**2/(2*(sin(x) + cos(x))*cos(x)) = (sin(x) + cos(x))/(2*cos(x)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  field_simp,
  ring_exp,
end

lemma Trigo_3_286_JAKW : -sin(pi/9)*sin(5*pi/36) + sin(13*pi/36)*sin(7*pi/18)=sqrt(2)/2:=
begin
  rw neg_mul,
  have : sin(pi/9)*sin(5*pi/36) = -cos(pi/4)/2 + cos(pi/36)/2,
  {
  rw mul_comm,
  rw sin_mul_sin,
  have : cos((5*pi/36) + (pi/9)) = cos (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((5*pi/36) - (pi/9)) = cos (pi/36),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(13*pi/36)*sin(7*pi/18) = -cos(3*pi/4)/2 + cos(pi/36)/2,
  {
  rw mul_comm,
  rw sin_mul_sin,
  have : cos((7*pi/18) + (13*pi/36)) = cos (3*pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((7*pi/18) - (13*pi/36)) = cos (pi/36),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : cos(3*pi/4) = -cos(pi/4),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/4) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_four,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_3_287_YBFG (h0 : -1 + sqrt(3) ≠ 0) : (tan(13*pi/12) + 1)/(tan(-pi/12) + 1)=sqrt(3):=
begin
  have : tan(13*pi/12) = tan(pi/12),
  {
  rw tan_eq_tan_add_int_mul_pi (13*pi/12) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(-pi/12) = -tan(pi/12),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_twelve,
  ring_exp,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_3_288_XIPK : sin(pi/12)*sin(5*pi/12)*cos(pi/6)=sqrt(3)/8:=
begin
  have : sin(5*pi/12) = cos(pi/12),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
  {
  have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
  {
  have : sin (pi/6) = sin(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  rw cos_pi_div_six,
  norm_num,
  field_simp,
  left,
  ring,
end

lemma Trigo_3_289_UNJI : cos(pi/18)*cos(11*pi/36) + cos(7*pi/36)*cos(4*pi/9)=sqrt(2)/2:=
begin
  have : cos(pi/18) = sin(4*pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(11*pi/36) = sin(7*pi/36),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw add_comm,
  rw mul_comm (sin(4*pi/9)) (sin(7*pi/36)),
  have : cos(7*pi/36)*cos(4*pi/9) + sin(7*pi/36)*sin(4*pi/9) = cos(-pi/4),
  {
  have : cos(-pi/4) = cos((7*pi/36) - (4*pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_sub,
  },
  rw this,
  have : cos(-pi/4) = cos(pi/4),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/4) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_four,
end

lemma Trigo_3_290_LCWZ : sin(pi/12)**2 + sin(pi/12)*cos(5*pi/12) + cos(5*pi/12)**2=3/2-3*sqrt(3)/4:=
begin
  have : cos(5*pi/12) = sin(pi/12),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(pi/12)**2 + sin(pi/12)*sin(pi/12) + sin(pi/12)**2 = 3*sin(pi/12)**2,
  {
  ring,
  },
  rw this,
  have : sin(pi/12)**2 = 1/2 - cos(pi/6)/2,
  {
  have : cos(pi/6) = cos(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  rw cos_pi_div_six,
  ring_exp,
end

lemma Trigo_3_291_TZIP : sin(7*pi/60)*cos(9*pi/20) - sin(9*pi/20)*cos(7*pi/60)=-sqrt(3)/2:=
begin
  rw sub_eq_neg_add,
  rw ← neg_mul,
  have : -sin(9*pi/20)*cos(7*pi/60) + sin(7*pi/60)*cos(9*pi/20) = sin(-pi/3),
  {
  have : sin(-pi/3) = sin((7*pi/60) - (9*pi/20)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  have : sin(-pi/3) = -sin(pi/3),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
  ring_exp,
end

lemma Trigo_3_292_OKQD : sin(pi/12)**2 - sin(pi/12)*cos(pi/12) + cos(pi/12)**2=3/4:=
begin
  rw sub_add_eq_add_sub,
  rw sin_sq_add_cos_sq,
  have : sin(pi/12)*cos(pi/12) = sin(pi/6)/2,
  {
  have : sin(pi/6) = 2*sin(pi/12)*cos(pi/12),
  {
  have : sin (pi/6) = sin(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_3_293_QSOH (h0 : sin(7*pi/18) ≠ 0) : (sin(pi/18) + sin(5*pi/18))/(sin(7*pi/36)*sin(11*pi/36))=2:=
begin
  have : sin(pi/18) + sin(5*pi/18) = 2*sin(pi/6)*cos(-pi/9),
  {
  rw sin_add_sin,
  have : sin(((pi/18) + (5*pi/18))/2) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos(((pi/18) - (5*pi/18))/2) = cos(-pi/9),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  have : cos(-pi/9) = sin(7*pi/18),
  {
  rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (-pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(11*pi/36) = cos(7*pi/36),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(7*pi/36)*cos(7*pi/36) = sin(7*pi/18)/2,
  {
  have : sin(7*pi/18) = 2*sin(7*pi/36)*cos(7*pi/36),
  {
  have : sin (7*pi/18) = sin(2*(7*pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_3_294_IBCI (h0 : sin(pi/9) ≠ 0) : cos(pi/18)*cos(4*pi/9)/sin(pi/9)=1/2:=
begin
  have : cos(pi/18)*cos(4*pi/9) = cos(pi/2)/2 + cos(-7*pi/18)/2,
  {
  rw cos_mul_cos,
  have : cos((pi/18) + (4*pi/9)) = cos (pi/2),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((pi/18) - (4*pi/9)) = cos (-7*pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw cos_pi_div_two,
  have : cos(-7*pi/18) = cos(7*pi/18),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(7*pi/18) = sin(8*pi/9),
  {
  rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(8*pi/9) = sin(pi/9),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_3_295_GTAO : sin(x) + cos(x)=sqrt(2)*sin(x+pi/4):=
begin
  have : sin(x + pi/4) = sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
  {
  have : sin(x+pi/4) = sin((x) + (pi/4)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_add,
  ring,
  },
  rw this,
  rw sin_pi_div_four,
  rw cos_pi_div_four,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_3_296_JKWR : 2*sin(pi/12)**2 - 1=-sqrt(3)/2:=
begin
  rw sub_eq_neg_add,
  have : -1 + 2*sin(pi/12)**2 = -cos(pi/6),
  {
  have : cos(pi/6) = 1 - 2*sin(pi/12)**2,
  {
  have : cos (pi/6) = cos(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  },
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  ring_exp,
end

lemma Trigo_3_297_XHXV (h0 : cos(13*pi/18) ≠ 0) : sin(pi/9)*sin(11*pi/18)/(-sin(31*pi/36)**2 + cos(31*pi/36)**2)=1/2:=
begin
  have : sin(pi/9)*sin(11*pi/18) = (cos(pi/2)-cos(13*pi/18))/2,
  {
  rw mul_comm,
  rw sin_mul_sin,
  have : cos((11*pi/18) + (pi/9)) = cos (13*pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((11*pi/18) - (pi/9)) = cos (pi/2),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw cos_pi_div_two,
  have : -sin(31*pi/36)**2 + cos(31*pi/36)**2 = cos(31*pi/18),
  {
  have : cos (31*pi/18) = cos(2*(31*pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : cos(31*pi/18) = -cos(13*pi/18),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (31*pi/18) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_3_298_EJGL : cos(pi/10)*cos(7*pi/30) - cos(4*pi/15)*cos(2*pi/5)=1/2:=
begin
  have : cos(2*pi/5) = sin(pi/10),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/5) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(4*pi/15) = sin(7*pi/30),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/15) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sub_eq_neg_add,
  rw mul_comm,
  rw ← neg_mul,
  have : -sin(pi/10)*sin(7*pi/30) + cos(pi/10)*cos(7*pi/30) = cos(pi/3),
  {
  have : cos(pi/3) = cos((pi/10) + (7*pi/30)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_add,
  ring,
  },
  rw this,
  rw cos_pi_div_three,
end

lemma Trigo_3_299_ROBF : -sin(-x + pi/4)**2 + cos(x - pi/4)**2=sin(2*x):=
begin
  have : cos(x - pi/4)**2 = 1/2 + cos(2*x - pi/2)/2,
  {
  have : cos(2*x - pi/2) = cos(2*(x - pi/4)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  have : sin(-x + pi/4)**2 = 1/2 - cos(-2*x + pi/2)/2,
  {
  have : cos(-2*x + pi/2) = cos(2*(-x + pi/4)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(-2*x + pi/2) = sin(2*x),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*x + pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos (2 * x - π / 2) = sin(2*x),
  {
  rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (2*x-pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  ring,
end