import trigo_import
open real
open_locale real
variables (x y : ℝ)

lemma Trigo_2_200_VKFM (h0 : cos (pi/8) ≠ 0) : 1/tan(pi/8)=1+sqrt(2):=
begin
  have : tan(pi/8)  =  sin(pi/4)/(1 + cos(pi/4)),
  {
  have : cos(pi/8) = cos((pi/4)/2),
  {
  apply congr_arg,
  ring,
  },
  rw this at *,
  have : tan(pi/8) = tan((pi/4)/2),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw tan_div_two',
  repeat {assumption},
  },
  rw this,
  rw cos_pi_div_four,
  rw sin_pi_div_four,
  norm_num,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end


lemma Trigo_2_201_HEEI : sin(pi/5)*cos(pi/30) - sin(3*pi/10)*cos(7*pi/15)=1/2:=
begin
  have : sin(3*pi/10)*cos(7*pi/15) = -sin(pi/6)/2 + sin(23*pi/30)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((7*pi/15) + (3*pi/10)) = sin (23*pi/30),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((7*pi/15) - (3*pi/10)) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(pi/5)*cos(pi/30)  =  sin(pi/6)/2 + sin(7*pi/30)/2,
  {
  rw sin_mul_cos,
  have : sin((pi/5) + (pi/30)) = sin (7*pi/30),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((pi/5) - (pi/30)) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  have : sin(7*pi/30)  =  sin(23*pi/30),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (7*pi/30) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_2_202_GVCN : -sqrt(3)*sin(x)/2 + cos(x)/2=sin(-x+pi/6):=
begin
  have : -sqrt(3)*sin(x)/2  =  -sin(x)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(x)/2  =  sin(pi/6)*cos(x),
  {
  field_simp,
  },
  rw this,
  have : -sin(x)*cos(pi/6) + sin(pi/6)*cos(x)  =  sin(-x + pi/6),
  {
  have : sin(-x+pi/6) = sin((pi/6) - (x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
end

lemma Trigo_2_203_KQQP (h0 : 2 - cos(pi/18)**2 ≠ 0) : (3 - cos(pi/9))/(2 - cos(pi/18)**2)=2:=
begin
  have : cos(pi/9)  =  -1 + 2*cos(pi/18)**2,
  {
  have : cos (pi/9) = cos(2*(pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  have : 3 - (-1 + 2 * cos (π / 18) ** 2) = 4 - 2*cos(pi/18)**2,
  {
    ring,
  },
  rw this,
  have : (4 - 2*cos(pi/18)**2)/(2 - cos(pi/18)**2)  =  2,
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
end

lemma Trigo_2_204_FKBX (h0 : cos(x) ≠ 0) (h1 : cos(2*x) ≠ 0) : 2*sin(2*x)*cos(x)**2/((cos(2*x) + 1)*cos(2*x))=tan(2*x):=
begin
  have :cos(2*x) + 1 =  2*cos(x)**2 ,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_two_mul,
  ring,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  field_simp,
  ring_exp,
end

lemma Trigo_2_205_KSQU : sqrt(cos(pi/3)/2 + 1/2)=sqrt(3)/2:=
begin
  rw cos_pi_div_three,
  norm_num,
  have : sqrt 4 = sqrt (2*2),
  {
    apply congr_arg,
    ring,
  },
  rw this,
  rw sqrt_mul_self,
  repeat {linarith},
end

lemma Trigo_2_206_KNLG (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(-x + 2*pi)*cos(-x + 11*pi/2)*cos(x + pi/2)*cos(x + pi)/(sin(-x - pi)*sin(-x + 3*pi)*sin(x + 9*pi/2)*cos(pi - x))=-tan(x):=
begin
  have : sin(-x + 2*pi) = -sin(x),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-x + 11*pi/2) = -sin(x),
  {
  rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 11*pi/2) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
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
  have : cos(x + pi) = -cos(x),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-x + 3*pi) = sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x + 3*pi) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-x - pi) = sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(x + 9*pi/2) = cos(x),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + 9*pi/2) (-3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(pi - x) = -cos(x),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_207_FKOY : 1 - 2*sin(5*pi/12)**2=-sqrt(3)/2:=
begin
  have : sin(5*pi/12) = cos(pi/12),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_twelve,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  norm_num,
  rw ← mul_assoc,
  rw ← sqrt_mul,
  have : sqrt(2*6) = sqrt(3) * sqrt(2*2),
  {
    rw ← sqrt_mul,
    apply congr_arg,
    norm_num,
    repeat {linarith},
  },
  rw this,
  rw sqrt_mul_self,
  ring,
  repeat {linarith},
end

lemma Trigo_2_208_GHHR (h0 : sin(pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : sin(pi/9) ≠ 0) : sqrt(3)/cos(pi/18) - 1/sin(17*pi/18)=-4:=
begin
  have : sin(17*pi/18) = sin(pi/18),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sqrt(3)/cos(pi/18) - 1/sin(pi/18) = (-cos(pi/18) + sqrt(3)*sin(pi/18))/(sin(pi/18)*cos(pi/18)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : sin(pi/18)*cos(pi/18) = sin(pi/9)/2,
  {
  have : sin(pi/9) = 2*sin(pi/18)*cos(pi/18),
  {
  have : sin (pi/9) = sin(2*(pi/18)),
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
  have : cos(pi/18) = 2*sin(pi/6)*cos(pi/18),
  {
  field_simp,
  },
  rw this,
  have : sqrt(3)*sin(pi/18) = 2*sin(pi/18)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  rw ← neg_mul,
  rw ← neg_mul,
  have : -2*sin(pi/6)*cos(pi/18) + 2*sin(pi/18)*cos(pi/6) = 2*sin(-pi/9),
  {
  have : sin(-pi/9) = sin(pi/18)*cos(pi/6) - sin(pi/6)*cos(pi/18),
  {
  have : sin(-pi/9) = sin((pi/18) - (pi/6)),
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
  have : sin(-pi/9) = -sin(pi/9),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_209_RURS (h0 : cos (x) ≠ 0) : (sin(x - pi/6) - sin(x + pi/6))/cos(x)=-1:=
begin
  have : sin(x - pi/6) - sin(x + pi/6) = -2*sin(pi/6)*cos(x),
  {
  have : -sin(x - pi/6) + sin(x + pi/6) = 2*sin(pi/6)*cos(x),
  {
  rw neg_add_eq_sub,
  rw sin_sub_sin,
  have : cos(((x + pi/6) + (x - pi/6))/2) = cos (x),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((x + pi/6) - (x - pi/6))/2) = sin(pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  have : -2*sin(pi/6) = -1,
  {
  have : sin(pi/6) = 1/2,
  {
  rw sin_pi_div_six,
  },
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
end

lemma Trigo_2_210_THJQ (h0 : cos(pi/9) ≥ 0) : sqrt(1 - sin(8*pi/9)**2)=-cos(8*pi/9):=
begin
  have : cos(8*pi/9) = -cos(pi/9),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
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
  rw ← cos_sq',
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h0,
  norm_num,
end

lemma Trigo_2_211_UWCA (h0 : cos(x) ≠ 0) : (sin(x + pi/6) + cos(x + pi/3))/(2*cos(x))=1/2:=
begin
  have : sin(x + pi/6) = cos(-x + pi/3),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (x + pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-x + pi/3) = sin(pi/3)*sin(x) + cos(pi/3)*cos(x),
  {
  have : cos(-x+pi/3) = cos((pi/3) - (x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_sub,
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
  rw cos_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_212_CWPH : (tan(pi/12) + 1)-sqrt(3)*(1 - tan(pi/12))=0:=
begin
  rw tan_pi_div_twelve,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_2_213_WZGF (h0 : 2 ≠ 0) (h1 : 4 ≠ 0) : sin(pi/18)*cos(pi/9)*cos(2*pi/9)=1/8:=
begin
  rw mul_assoc,
  have : cos(pi/9)*cos(2*pi/9) = cos(pi/3)/2 + cos(-pi/9)/2,
  {
  rw cos_mul_cos,
  have : cos((pi/9) + (2*pi/9)) = cos (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((pi/9) - (2*pi/9)) = cos (-pi/9),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : cos(-pi/9) = cos(pi/9),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  have : sin(pi/18) = cos(4*pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(4*pi/9)*(1/2/2 + cos(pi/9)/2) = cos(4*pi/9)/4 + cos(pi/9)*cos(4*pi/9)/2,
  {
  ring_exp,
  },
  rw this,
  have : cos(pi/9)*cos(4*pi/9)/2 = cos(5*pi/9)/4 + cos(pi/3)/4,
  {
  have : cos(pi/9)*cos(4*pi/9) = cos(pi/3)/2 + cos(5*pi/9)/2,
  {
  rw mul_comm,
  rw cos_mul_cos,
  have : cos((4*pi/9) + (pi/9)) = cos (5*pi/9),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((4*pi/9) - (pi/9)) = cos (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  have : cos(5*pi/9) = -cos(4*pi/9),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_214_HHTA (h0 : cos (pi/8) ≠ 0) (h1: 2 + sqrt(2) ≠ 0) : tan(pi/8) - 1/tan(pi/8)=-2:=
begin
  have : tan(pi/8) = sin(pi/4)/(1+cos(pi/4)),
  {
  have : cos(pi/8) = cos((pi/4)/2),
  {
  apply congr_arg,
  ring,
  },
  rw this at *,
  have : tan(pi/8) = tan((pi/4)/2),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw tan_div_two',
  repeat {assumption},
  },
  rw this,
  rw cos_pi_div_four,
  rw sin_pi_div_four,
  norm_num,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_2_215_CBML : sin(4*pi/45)*sin(56*pi/45) + sin(23*pi/90)*cos(4*pi/45)=1/2:=
begin
  have : sin(56*pi/45) = -sin(11*pi/45),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (56*pi/45) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(23*pi/90) = cos(11*pi/45),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (23*pi/90) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_neg,
  rw ← neg_mul,
  rw mul_comm (cos(11*π/45)) (cos(4*π/45)),
  have : -sin(4*pi/45)*sin(11*pi/45) + cos(4*pi/45)*cos(11*pi/45) = cos(pi/3),
  {
  have : cos(pi/3) = cos((4*pi/45) + (11*pi/45)),
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

lemma Trigo_2_216_YACW (h0: sin(pi/9) ≠ 0) : sin(-13*pi/9)*cos(4*pi/9)/(-sin(7*pi/36)**2 + cos(29*pi/36)**2)=1/2:=
begin
  have : cos(29*pi/36) = -cos(7*pi/36),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (29*pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw neg_sq,
  have : -sin(7*pi/36)**2 + cos(7*pi/36)**2 = cos(7*pi/18),
  {
  have : cos (7*pi/18) = cos(2*(7*pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : cos(7*pi/18) = sin(pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-13*pi/9) = sin(4*pi/9),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-13*pi/9) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
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
  field_simp,
  ring_exp,
end

lemma Trigo_2_217_NWBU (h0: -sin 1 + cos 1 ≤ 0) (h1:cos 1 ≥ 0) : 2*sqrt(1 - sin(2)) + sqrt(2*cos(2) + 2)=2*sin(1):=
begin
  have : 1 - sin(2) = cos(1)**2 + sin(1)**2 - sin(2),
  {
  rw cos_sq_add_sin_sq,
  },
  rw this,
  have : sin(2) = 2*sin(1)*cos(1),
  {
  have : sin (2) = sin(2*(1)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : cos(1)**2 + sin(1)**2 - 2*sin(1)*cos(1) = (-sin(1) + cos(1))**2,
  {
  ring_exp,
  },
  rw this,
  have : cos(2) = 2*cos(1)**2 - 1,
  {
  have : cos (2) = cos(2*(1)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  },
  rw this,
  ring,
  rw sqrt_sq_eq_abs,
  rw abs_eq_neg_self.mpr h0,
  rw sqrt_mul,
  have : sqrt 4 = sqrt (2**2),
  {
    apply congr_arg,
    norm_num,
  },
  rw this,
  repeat {rw sqrt_sq},
  ring,
  repeat{linarith},
end

lemma Trigo_2_218_JEUS (h0 : cos(pi/12) ≠ 0) (h1 : -sin(π/12)**2 + cos(π/12)**2 ≠ 0) : tan(pi/12)/(1 - tan(pi/12)**2)=sqrt(3)/6:=
begin
  rw tan_eq_sin_div_cos,
  rw div_pow,
  have : 1 - sin(pi/12)**2/cos(pi/12)**2 = (-sin(pi/12)**2 + cos(pi/12)**2)/cos(pi/12)**2,
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : sin(π/12)/cos(π/12)/((-sin(π/12)**2 + cos(π/12)**2)/cos(π/12)**2) = sin(π/12)*cos(π/12)/(-sin(π/12)**2 + cos(π/12)**2),
  {
    field_simp,
    ring_exp,
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
  rw sin_pi_div_six,
  rw cos_pi_div_six,
  norm_num,
  have : sqrt 3 ≠ 0,
  {
    rw sqrt_ne_zero,
    repeat {linarith},
  },
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_2_219_KWSA (h0 : cos(3*pi/20) ≠ 0) (h1 : cos(pi/10) ≠ 0) (h2 : 1 - tan(pi/10) * tan(3*pi/20) ≠ 0) : tan(pi/10)*tan(3*pi/20) + tan(pi/10) + tan(3*pi/20)=1:=
begin
  rw add_assoc,
  have : tan(pi/10) + tan(3*pi/20) = (-tan(pi/10)*tan(3*pi/20) + 1)*tan(pi/4),
  {
  rw tan_add_tan,
  have : tan((pi/10) + (3*pi/20)) = tan (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(pi/10)*tan(3*pi/20) + 1)*tan(pi/4) = -tan(pi/10)*tan(3*pi/20)*tan(pi/4) + tan(pi/4),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_four, -cos_pi_div_four, -sin_pi_div_two, -cos_pi_div_two],
  },
  rw this,
  rw tan_pi_div_four,
  norm_num,
end

lemma Trigo_2_220_ZJNX : -sin(29*pi/180)*sin(91*pi/180) + sin(119*pi/180)*sin(181*pi/180)=-1/2:=
begin
  have : sin(119*pi/180) = cos(29*pi/180),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (119*pi/180) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(181*pi/180) = -sin(pi/180),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (181*pi/180) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(91*pi/180) = cos(pi/180),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (91*pi/180) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_neg,
  rw ← sub_eq_add_neg,
  rw mul_comm (cos(29*pi/180)) (sin(pi/180)),
  have : -sin(29*pi/180)*cos(pi/180) - sin(pi/180)*cos(29*pi/180) = -sin(pi/6),
  {
  have : sin(pi/6) = sin(pi/180)*cos(29*pi/180) + sin(29*pi/180)*cos(pi/180),
  {
  have : sin(pi/6) = sin((pi/180) + (29*pi/180)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
  },
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_2_221_IETY (h0 : cos(2) ≠ 0) : sin(-2) + cos(2 - pi)*tan(2 - 4*pi)=-2*sin(2):=
begin
  have : cos(2 - pi) = -cos(2),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2 - pi) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : tan(2 - 4*pi) = tan(2),
  {
  rw tan_eq_tan_add_int_mul_pi (2 - 4*pi) (4),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  field_simp,
  ring_exp,
end

lemma Trigo_2_222_ZDRD : sin(31*pi/90)*cos(29*pi/90) + sin(61*pi/90)*cos(31*pi/90)=sqrt(3)/2:=
begin
  have : sin(61*pi/90)*cos(31*pi/90) = sin(46*pi/45)/2 + sin(pi/3)/2,
  {
  rw sin_mul_cos,
  have : sin((61*pi/90) + (31*pi/90)) = sin (46*pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((61*pi/90) - (31*pi/90)) = sin (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(46*pi/45) = -sin(pi/45),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (46*pi/45) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : -sin(pi/45)/2 + sin(pi/3)/2 = sin(7*pi/45)*cos(8*pi/45),
  {
  have : -sin(pi/45) + sin(pi/3) = 2*sin(7*pi/45)*cos(8*pi/45),
  {
  rw neg_add_eq_sub,
  rw sin_sub_sin,
  have : cos(((pi/3) + (pi/45))/2) = cos (8*pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((pi/3) - (pi/45))/2) = sin(7*pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  have : sin(7*pi/45) = cos(31*pi/90),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/45) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(8*pi/45) = sin(29*pi/90),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (8*pi/45) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw add_comm,
  rw mul_comm (cos(31*π/90)) (sin(29*π/90)),
  have : sin(29*pi/90)*cos(31*pi/90) + sin(31*pi/90)*cos(29*pi/90) = sin(2*pi/3),
  {
  have : sin(2*pi/3) = sin((29*pi/90) + (31*pi/90)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
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
  rw sin_pi_div_three,
end

lemma Trigo_2_223_RDSG (h0 : cos(x) ≠ 0) : sin(x - 2*pi)*cos(-x + 2*pi)*cos(x - pi/2)/sin(x + 5*pi/2)=sin(x)**2:=
begin
  have : sin(x - 2*pi) = sin(x),
  {
  rw sin_eq_sin_add_int_mul_two_pi (x - 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-x + 2*pi) = cos(x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(x - pi/2) = sin(x),
  {
  rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (x - pi/2) (0),
  repeat {apply congr_arg _},
  simp,
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
  field_simp,
  ring_exp,
end

lemma Trigo_2_224_VDAS : -sin(pi/3)**2 + sqrt(3)*sin(2*pi/3)/2=0:=
begin
  rw sin_pi_div_three,
  rw sin_two_pi_div_three,
  norm_num,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_2_225_YWGR (h0 : cos(pi/18) ≠ 0) : (-sin(pi/36)**2 + cos(pi/36)**2)/(sin(2*pi/9)*cos(2*pi/9))=2:=
begin
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
  have : sin(4*pi/9) = cos(pi/18),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_2_226_DVUW : (sin(pi/12) - cos(pi/12))*(sin(pi/12) + cos(pi/12))=-sqrt(3)/2:=
begin
  have : (sin(pi/12) - cos(pi/12))*(sin(pi/12) + cos(pi/12)) = -cos(pi/12)**2 + sin(pi/12)**2,
  {
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
  have : -cos(pi/6) = -sqrt(3)/2,
  {
  have : cos(pi/6) = sqrt(3)/2,
  {
  rw cos_pi_div_six,
  },
  linarith,
  },
  rw this,
end

lemma Trigo_2_227_EXKN : sin(4*pi/3)*cos(19*pi/6)*tan(21*pi/4)=3/4:=
begin
  have : sin(4*pi/3) = -sin(pi/3),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4*pi/3) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
  have : cos(19*pi/6) = -cos(pi/6),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (19*pi/6) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  have : tan(21*pi/4) = tan(pi/4),
  {
  rw tan_eq_tan_add_int_mul_pi (21*pi/4) (-5),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_four,
  norm_num,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_2_228_OWVU (h0: cos(2) ≤ 0) : sqrt(2*cos(4) + 2)=-2*cos(2):=
begin
  have : cos(4) = -1 + 2*cos(2)**2,
  {
  have : cos(4) = cos(2*(2)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  ring_exp,
  rw sqrt_mul',
  have : sqrt(4)= sqrt(2**2),
  {
    apply congr_arg,
    ring,
  },
  rw this,
  repeat {rw sqrt_sq_eq_abs},
  rw abs_eq_neg_self.mpr h0,
  rw abs_eq_self.mpr,
  ring,
  repeat {linarith},
end

lemma Trigo_2_229_KMZX (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : tan(x) + 1/tan(x)=2/sin(2*x):=
begin
  rw tan_eq_sin_div_cos,
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
  rw one_div_div,
  have : sin(x)/cos(x) + cos(x)/sin(x) = (sin(x)**2 + cos(x)**2)/(sin(x)*cos(x)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  field_simp,
  ring_exp,
end

lemma Trigo_2_230_NIZW : 2*sin(x)**2 + cos(2*x) + 1=2:=
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
  ring,
  rw ← add_assoc,
  rw sin_sq_add_cos_sq,
  norm_num,
end

lemma Trigo_2_231_MJDQ : sin(7*pi/36)*sin(4*pi/9) + cos(7*pi/36)*cos(4*pi/9)=sqrt(2)/2:=
begin
  rw add_comm,
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

lemma Trigo_2_232_WIUI : cos(3*x) + cos(5*x)=2*cos(4*x)*cos(x):=
begin
  rw mul_assoc,
  have : cos(4*x)*cos(x) = cos(3*x)/2 + cos(5*x)/2,
  {
  rw cos_mul_cos,
  have : cos((4*x) + (x)) = cos (5*x),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((4*x) - (x)) = cos (3*x),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  ring_exp,
end

lemma Trigo_2_233_EOKP (h0 : -cos(2) + sin(2) ≥ 0) (h1 : cos(2) ≤ 0) : 2*sqrt(1 - sin(4)) + sqrt(2*cos(4) + 2)=2*sin(2)-4*cos(2):=
begin
  have : cos(4) = 2*cos(2)**2 - 1,
  {
  have : cos (4) = cos(2*(2)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  },
  rw this,
  ring,
  rw sqrt_mul,
  have : sqrt(4) = sqrt(2**2),
  {
    apply congr_arg,
    ring,
  },
  rw this,
  repeat {rw sqrt_sq_eq_abs},
  rw abs_eq_neg_self.mpr h1,
  rw abs_eq_self.mpr,
  have : sin(4) = 2*sin(2)*cos(2),
  {
  have : sin (4) = sin(2*(2)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : 1 - 2*sin(2)*cos(2) = cos(2)**2 + sin(2)**2 - 2*sin(2)*cos(2),
  {
  rw cos_sq_add_sin_sq,
  },
  rw this,
  have : cos(2)**2 + sin(2)**2 - 2*sin(2)*cos(2) = (-cos(2) + sin(2))**2,
  {
  ring_exp,
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h0,
  norm_num,
  ring_exp,
  repeat{linarith},
end

lemma Trigo_2_234_GIRS (h0 : cos((x*4 + π)/4) ≠ 0) (h1 : sin((x*4 + π)/4) ≠ 0) (h2 : cos(2*x) ≠ 0) : (4*cos(x)**4 - 2*cos(2*x) - 1)/(cos(x + pi/4)**2*tan(x + pi/4))=2*cos(2*x):=
begin
  rw sub_right_comm,
  have : 4*cos(x)**4 - 1 = (2*cos(x)**2 - 1)*(2*cos(x)**2 + 1),
  {
  ring_exp,
  },
  rw this,
  have : 2*cos(x)**2 - 1 = cos(2*x),
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  },
  rw this,
  have : cos(2*x)*(2*cos(x)**2 + 1) - 2*cos(2*x) = (2*cos(x)**2 - 1)*cos(2*x),
  {
  ring_exp,
  },
  rw this,
  have : 2*cos(x)**2 - 1 = cos(2*x),
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  have : cos(2*x)*cos(2*x)/(cos(x + π/4)**2*(sin(x + π/4)/cos(x + π/4))) = cos(2*x)*cos(2*x)/(cos(x + π/4)*sin(x + π/4)),
  {
    field_simp,
    ring,
  },
  rw this,
  rw mul_comm (cos(x + π/4)) (sin(x + π/4)),
  have : sin(x + pi/4)*cos(x + pi/4) = sin(2*x + pi/2)/2,
  {
  have : sin(2*x + pi/2) = 2*sin(x + pi/4)*cos(x + pi/4),
  {
  have : sin (2*x + pi/2) = sin(2*(x + pi/4)),
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
  have : sin(2*x + pi/2) = cos(2*x),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (2*x + pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_2_235_PZHG : sin(pi/18)*cos(pi/9) + sin(4*pi/9)*sin(8*pi/9)=1/2:=
begin
  have : sin(4*pi/9) = cos(pi/18),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
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
  rw mul_comm (cos(π/18)) (sin(π/9)),
  have : sin(pi/18)*cos(pi/9) + sin(pi/9)*cos(pi/18) = sin(pi/6),
  {
  have : sin(pi/6) = sin((pi/9) + (pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
  },
  rw this,
  rw sin_pi_div_six,
end

lemma Trigo_2_236_IXFH (h0 : 3 - cos(π/9) ≠ 0) : (3 - cos(pi/9))/(2 - sin(4*pi/9)**2)=2:=
begin
  have : sin(4*pi/9)**2 = 1/2 - cos(8*pi/9)/2,
  {
  have : cos (8*pi/9) = cos(2*(4*pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(8*pi/9) = -cos(pi/9),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : 2 - (1/2 - -cos(π/9)/2) = (3 - cos(π/9))/2,
  {
    ring,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_2_237_BRIA (h0 : 2 ≠ 0) : 2*sin(-x + pi/4)*sin(x + pi/4)=cos(2*x):=
begin
  have : sin(-x + pi/4) = -sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
  {
  have : sin(-x+pi/4) = sin((pi/4) - (x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
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
  rw cos_pi_div_four,
  rw sin_pi_div_four,
  have : -sin(x)*(sqrt(2)/2) + sqrt(2)/2*cos(x) = sqrt(2)*(-sin(x) + cos(x))/2,
  {
  ring_exp,
  },
  rw this,
  have : sin(x)*(sqrt(2)/2) + sqrt(2)/2*cos(x) = sqrt(2)*(sin(x) + cos(x))/2,
  {
  ring_exp,
  },
  rw this,
  have : cos(2*x) = -sin(x)**2 + cos(x)**2 ,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_2_238_XBJI (h0 : 1 - sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : cos(x)/(1 - sin(x))-(1+sin(x))/cos(x)=0:=
begin
  have : cos(x)/(1 - sin(x)) - (1 + sin(x))/cos(x) = (cos(x)**2 - (sin(x) + 1)*(1 - sin(x)))/((1 - sin(x))*cos(x)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : (sin(x) + 1)*(1 - sin(x)) = 1 - sin(x)**2,
  {
  ring_exp,
  },
  rw this,
  rw ← cos_sq',
  norm_num,
end

lemma Trigo_2_239_HRKH (h0 : 1 - tan(5*pi/18) * tan(7*pi/18) ≠ 0) (h1 : cos(7*pi/18) ≠ 0) (h2 : cos(5*pi/18) ≠ 0) : -sqrt(3)*tan(5*pi/18)*tan(7*pi/18) + tan(5*pi/18) + tan(7*pi/18)=-sqrt(3):=
begin
  rw add_assoc,
  have : tan(5*pi/18) + tan(7*pi/18) = (-tan(5*pi/18)*tan(7*pi/18) + 1)*tan(2*pi/3),
  {
  rw tan_add_tan,
  have : tan((5*pi/18) + (7*pi/18)) = tan (2*pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(5*pi/18)*tan(7*pi/18) + 1)*tan(2*pi/3) = tan(2*pi/3) - tan(5*pi/18)*tan(7*pi/18)*tan(2*pi/3),
  {
  ring_exp,
  },
  rw this,
  have : tan(2*pi/3) = -tan(pi/3),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_three,
  norm_num,
  ring_exp,
end

lemma Trigo_2_240_EXWT (h0 : sin(pi/9) ≠ 0) : (sin(7*pi/36)**2 - 1/2)/sin(pi/9)=-1/2:=
begin
  have : sin(7*pi/36)**2 = 1/2 - cos(7*pi/18)/2,
  {
  have : cos (7*pi/18) = cos(2*(7*pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(7*pi/18) = sin(pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_241_JCOO (h0 : cos(2*x) ≠ 0) (h1 : sin (2 * x) + cos (2 * x) ≠ 0) (h2 : -sin(2*x) + cos(2*x) ≠ 0) : (-2*sin(2*x)*cos(2*x) + 1)/(-sin(2*x)**2 + cos(2*x)**2)=(1-tan(2*x))/(1+tan(2*x)):=
begin
  have : -2*sin(2*x)*cos(2*x) + 1 = sin(2*x)**2 - 2*sin(2*x)*cos(2*x) + cos(2*x)**2,
  {
  have : -2*sin(2*x)*cos(2*x) + 1 = -2*sin(2*x)*cos(2*x) + (sin(2*x)**2 + cos(2*x)**2),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(2*x)**2 - 2*sin(2*x)*cos(2*x) + cos(2*x)**2 = (-sin(2*x) + cos(2*x))**2,
  {
  ring_exp,
  },
  rw this,
  have : -sin(2*x)**2 + cos(2*x)**2 = (-sin(2*x) + cos(2*x))*(sin(2*x) + cos(2*x)),
  {
  ring_exp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  have : 1 + sin(2*x)/cos(2*x) = (sin(2*x) + cos(2*x))/cos(2*x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : 1 - sin(2*x)/cos(2*x) = (-sin(2*x) + cos(2*x))/cos(2*x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_2_242_LQDW (h0 : 2 - sqrt(3) ≠ 0) : (tan(7*pi/12) + 1) + (2 + sqrt(3))*(tan(-pi/12) + 1)=0:=
begin
  have : tan(7*pi/12) = -1/tan(pi/12),
  {
  rw tan_eq_neg_one_div_tan_add_pi_div_two_add_int_mul_pi (7*pi/12) (-1),
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
  field_simp,
  ring_exp,
  have : -sqrt(3)**3 = -sqrt(3) * sqrt(3)**2,
  {
    ring,
  },
  rw this,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_2_243_PTCJ (h0 : sin(pi/11) ≠ 0) : cos(pi/11)*cos(2*pi/11)*cos(3*pi/11)*cos(4*pi/11)*cos(5*pi/11)=1/2**5:=
begin
  have : cos(pi/11) = sin(2*pi/11)/(2*sin(pi/11)),
  {
  have : sin (2*pi/11) = sin(2*(pi/11)),
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
  rw div_mul_eq_mul_div,
  have : sin(2*pi/11)*cos(2*pi/11) = sin(4*pi/11)/2,
  {
  have : sin(4*pi/11) = 2*sin(2*pi/11)*cos(2*pi/11),
  {
  have : sin (4*pi/11) = sin(2*(2*pi/11)),
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
  have : sin(4*π/11)/2/(2*sin(π/11))*cos(3*π/11)*cos(4*π/11) = sin(4*π/11)*cos(4*π/11)/2/(2*sin(π/11))*cos(3*π/11),
  {
    ring,
  },
  rw this,
  have : sin(4*pi/11)*cos(4*pi/11) = sin(8*pi/11)/2,
  {
  have : sin(8*pi/11) = 2*sin(4*pi/11)*cos(4*pi/11),
  {
  have : sin (8*pi/11) = sin(2*(4*pi/11)),
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
  have : cos(3*pi/11) = -cos(8*pi/11),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/11) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(8*π/11)/2/2/(2*sin(π/11))*-cos(8*π/11) = -(sin(8*π/11)*cos(8*π/11)/2/2/(2*sin(π/11))),
  {
    ring,
  },
  rw this,
  have : sin(8*pi/11)*cos(8*pi/11) = sin(16*pi/11)/2,
  {
  have : sin(16*pi/11) = 2*sin(8*pi/11)*cos(8*pi/11),
  {
  have : sin (16*pi/11) = sin(2*(8*pi/11)),
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
  have : sin(16*pi/11) = -sin(5*pi/11),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (16*pi/11) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have :  -(-sin(5*π/11)/2/2/2/(2*sin(π/11)))*cos(5*π/11) = sin(5*π/11)*cos(5*π/11)/2/2/2/(2*sin(π/11)),
  {
    ring,
  },
  rw this,
  have : sin(5*pi/11)*cos(5*pi/11) = sin(10*pi/11)/2,
  {
  have : sin(10*pi/11) = 2*sin(5*pi/11)*cos(5*pi/11),
  {
  have : sin (10*pi/11) = sin(2*(5*pi/11)),
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
  have : sin(10*pi/11) = sin(pi/11),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (10*pi/11) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_244_ULZV (h0 : sin(x) ≠ 0) (h1 : tan(x) ≠ 0) : sin(x - pi/2)*cos(x + 3*pi/2)*tan(pi - x)/(sin(-x - pi)*tan(-x - pi))=-cos(x):=
begin
  have : sin(x - pi/2) = -cos(x),
  {
  rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (x - pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(x + 3*pi/2) = sin(x),
  {
  rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (x + 3*pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(pi - x) = -tan(x),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (pi - x) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(-x - pi) = sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(-x - pi) = -tan(x),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_245_DXOK : (sin(pi/6)*cos(pi/2) - 2*sin(pi/3)*cos(pi) - tan(pi/4))/(sin(pi) + 2*cos(pi/6)*tan(pi/3) - sqrt(3)*tan(pi/6))=(sqrt(3)-1)/2:=
begin
  rw tan_pi_div_four,
  rw sin_pi_div_six,
  rw cos_pi_div_two,
  rw sin_pi_div_three,
  rw cos_pi,
  rw tan_pi_div_six,
  rw sin_pi,
  rw cos_pi_div_six,
  rw tan_pi_div_three,
  norm_num,
  ring_exp,
  rw sq_sqrt,
  field_simp,
  ring,
  repeat {linarith},
end

lemma Trigo_2_246_FANN : sin(x - y)-sin(x)*cos(y)+cos(x)*sin(y)=0:=
begin
  rw sub_eq_add_neg,
  rw add_assoc,
  rw ← neg_mul,
  rw mul_comm (cos(x)) (sin(y)),
  have : -sin(x)*cos(y) + sin(y)*cos(x) = sin(-x + y),
  {
  have : sin(-x+y) = sin((y) - (x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  have : sin(-x + y) = -sin(x - y),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + y) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
end

lemma Trigo_2_247_BOSW : sin(pi/12)**2 - cos(pi/12)**2=-sqrt(3)/2:=
begin
  rw sub_eq_neg_add,
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
  rw cos_pi_div_six,
  ring_exp,
end

lemma Trigo_2_248_FOFC (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(pi - x)*cos(-x + 2*pi)*tan(-x + 3*pi/2)/(sin(-x - pi)*tan(x + pi/2))=-cos(x):=
begin
  have : sin(pi - x) = sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-x + 2*pi) = cos(x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : tan(-x + 3*pi/2) = 1/tan(x),
  {
  rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-x + 3*pi/2) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-x - pi) = sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  repeat {rw tan_eq_sin_div_cos},
  have : sin(x + pi/2) = cos(x),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
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
  field_simp,
  ring_exp,
end

lemma Trigo_2_249_YOAQ (h0 : sqrt(3) - 1 ≠ 0) : (tan(pi/12) + 1)/(tan(11*pi/12) + 1) - sin(pi/9)*sin(11*pi/18) + cos(-7*pi/18)*cos(pi/9)=sqrt(3):=
begin
  have : sin(11*pi/18) = sin(7*pi/18),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (11*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-7*pi/18) = cos(7*pi/18),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sub_eq_add_neg,
  rw add_assoc,
  rw ← neg_mul,
  rw mul_comm (cos(7*π/18)) (cos(π/9)),
  have : -sin(pi/9)*sin(7*pi/18) + cos(pi/9)*cos(7*pi/18) = cos(pi/2),
  {
  have : cos(pi/2) = cos((pi/9) + (7*pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_add,
  ring,
  },
  rw this,
  rw cos_pi_div_two,
  have : tan(11*pi/12) = -tan(pi/12),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (11*pi/12) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_twelve,
  norm_num,
  have : sqrt(3) - 2 + 1 = sqrt(3) - 1,
  {
    ring,
  },
  rw this,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end