import trigo_import
open real
open_locale real
variables (x y : ℝ)

lemma Trigo_4_300_HVNS (h0 : sin(2*pi/9) ≥ 0) (h1 : sin(2*pi/9) ≠ 0) : (sqrt(3)*sin(pi/18) + cos(pi/18))/sqrt(1 - cos(4*pi/9))=sqrt(2):=
begin
  have : sqrt(3)*sin(pi/18)  =  2*sin(pi/18)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/18)  =  2*sin(pi/6)*cos(pi/18),
  {
  field_simp,
  },
  rw this,
  have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18)  =  2*sin(2*pi/9),
  {
  have : sin(2*pi/9) = sin(pi/18)*cos(pi/6) + sin(pi/6)*cos(pi/18),
  {
  have : sin(2*pi/9) = sin((pi/6) + (pi/18)),
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
  have : 1 - cos (4 * π / 9) = sin(2*pi/9)**2 + cos(2*pi/9)**2 - cos(4*pi/9),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : cos(4*pi/9)  =  -sin(2*pi/9)**2 + cos(2*pi/9)**2,
  {
  have : cos (4*pi/9) = cos(2*(2*pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : sin(2*π/9)**2 + cos(2*π/9)**2 - (-sin(2*π/9)**2 + cos(2*π/9)**2) = 2*sin(2*pi/9)**2,
  {
  ring,
  } ,
  rw this,
  rw sqrt_mul,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h0,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_4_301_SLSZ : sin(pi/12) - sqrt(3)*cos(pi/12)=-sqrt(2):=
begin
  have : sqrt(3)*cos(pi/12)  =  2*sin(pi/3)*cos(pi/12),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : sin(pi/12)  =  2*sin(pi/12)*cos(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  rw sub_eq_neg_add,
  rw ← neg_mul,
  rw ← neg_mul,
  have : -2*sin(pi/3)*cos(pi/12) + 2*sin(pi/12)*cos(pi/3)  =  2*sin(-pi/4),
  {
  have : sin(-pi/4) = sin(pi/12)*cos(pi/3) - sin(pi/3)*cos(pi/12),
  {
  have : sin(-pi/4) = sin((pi/12) - (pi/3)),
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
  have : sin(-pi/4)  =  -sin(pi/4),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/4) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_four,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_4_302_SHAD (h0 : cos(2*pi/9) ≠ 0) (h1 : 1 - tan(pi/9) * tan(2*pi/9) ≠ 0) (h2 : cos(pi/9) ≠ 0) : sqrt(3)*tan(pi/9)*tan(2*pi/9) + tan(pi/9) + tan(2*pi/9)=sqrt(3):=
begin
  rw add_assoc,
  have : tan(pi/9) + tan(2*pi/9)  =  (-tan(pi/9)*tan(2*pi/9) + 1)*tan(pi/3),
  {
  rw tan_add_tan,
  have : tan((pi/9) + (2*pi/9)) = tan (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  rw tan_pi_div_three,
  have : (-tan(pi/9)*tan(2*pi/9) + 1)*sqrt(3)  =  -sqrt(3)*tan(pi/9)*tan(2*pi/9) + sqrt(3),
  {
  ring_exp,
  },
  rw this,
  norm_num,
end

lemma Trigo_4_303_WCHH (h0 : 1 - tan(5*pi/36) * tan(7*pi/36) ≠ 0) (h1 : cos(5*pi/36) ≠ 0) (h2 : cos(7*pi/36) ≠ 0) : sqrt(3)*tan(5*pi/36)*tan(7*pi/36) + tan(5*pi/36) + tan(7*pi/36)=sqrt(3):=
begin
  rw add_assoc,
  have : tan(5*pi/36) + tan(7*pi/36)  =  (-tan(5*pi/36)*tan(7*pi/36) + 1)*tan(pi/3),
  {
  rw tan_add_tan,
  have : tan((5*pi/36) + (7*pi/36)) = tan (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  rw tan_pi_div_three,
  have : (-tan(5*pi/36)*tan(7*pi/36) + 1)*sqrt(3)  =  -sqrt(3)*tan(5*pi/36)*tan(7*pi/36) + sqrt(3),
  {
  ring_exp,
  },
  rw this,
  norm_num,
end

lemma Trigo_4_304_VPTQ (h0 : cos(pi/18) ≠ 0) (h1 : sin(4*pi/9) ≠ 0) : (sqrt(3)*tan(pi/18) + 1)*(cos(pi/9)**2 - 1/2)=1/2:=
begin
  have : cos(pi/9)**2 - 1/2  =  cos(2*pi/9)/2,
  {
  have : cos(2*pi/9) = 2*cos(pi/9)**2 - 1,
  {
  have : cos (2*pi/9) = cos(2*(pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  },
  linarith,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  have : sqrt(3)*(sin(pi/18)/cos(pi/18)) + 1  =  (sqrt(3)*sin(pi/18) + cos(pi/18))/cos(pi/18),
  {
  field_simp,
  },
  rw this,
  have : sqrt(3)*sin(pi/18)  =  2*cos(pi/6)*sin(pi/18),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/18)  =  2*sin(pi/6)*cos(pi/18),
  {
  field_simp,
  },
  rw this,
  rw mul_right_comm,
  have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18)  =  2*sin(2*pi/9),
  {
  have : sin(2*pi/9) = sin(pi/18)*cos(pi/6) + sin(pi/6)*cos(pi/18),
  {
  have : sin(2*pi/9) = sin((pi/6) + (pi/18)),
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
  rw div_mul_eq_mul_div,
  have : 2*sin(2*π/9)*(cos(2*π/9)/2)/(2*sin(π/6)*cos(π/18)) = sin(2*pi/9)*cos(2*pi/9)/(2*sin(π/6)*cos(π/18)),
  {
  ring,
  },
  rw this,
  have : sin(2*pi/9)*cos(2*pi/9)  =  sin(4*pi/9)/2,
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
  have : cos(pi/18)  =  sin(4*pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_4_305_XJWQ : sin(77*pi/180)*cos(29*pi/90) + sin(347*pi/180)*cos(37*pi/45)=sqrt(2)/2:=
begin
  have : sin(347*pi/180)  =  -cos(77*pi/180),
  {
  rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (347*pi/180) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(29*pi/90)  =  sin(8*pi/45),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (29*pi/90) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : -cos(77*pi/180)*cos(37*pi/45)  =  -cos(71*pi/180)/2 - cos(5*pi/4)/2,
  {
  have : cos(77*pi/180)*cos(37*pi/45) = cos(71*pi/180)/2 + cos(5*pi/4)/2,
  {
  rw mul_comm,
  rw cos_mul_cos,
  have : cos((37*pi/45) + (77*pi/180)) = cos (5*pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((37*pi/45) - (77*pi/180)) = cos (71*pi/180),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  have : sin(77*pi/180)*sin(8*pi/45)  =  -cos(109*pi/180)/2 + cos(pi/4)/2,
  {
  rw sin_mul_sin,
  have : cos((77*pi/180) + (8*pi/45)) = cos (109*pi/180),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((77*pi/180) - (8*pi/45)) = cos (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : cos(109*pi/180)  =  -cos(71*pi/180),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (109*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(5*pi/4)  =  -cos(pi/4),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (5*pi/4) (-1),
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

lemma Trigo_4_306_QRTB : sin(pi/4)**2 + sin(pi/2) - cos(pi/4)**2=1:=
begin
  rw ← sub_add_eq_add_sub,
  have : sin(pi/4)**2 - cos(pi/4)**2  =  -cos(pi/2),
  {
  have : cos(pi/2) = -sin(pi/4)**2 + cos(pi/4)**2,
  {
  have : cos (pi/2) = cos(2*(pi/4)),
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
  rw cos_pi_div_two,
  rw sin_pi_div_two,
  norm_num,
end

lemma Trigo_4_307_ICEX (h0 : sqrt(3) ≠ 0) : (-2*cos(-17*pi/6) + 4*cos(-17*pi/12)**4 - 1)/(cos(-7*pi/6)**2*tan(-7*pi/6))=-sqrt(3):=
begin
  have : cos(-17*pi/12)  =  -cos(5*pi/12),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-17*pi/12) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-17*pi/6)  =  -cos(pi/6),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-17*pi/6) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-7*pi/6)  =  -cos(pi/6),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-7*pi/6) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(-7*pi/6)  =  -tan(pi/6),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-7*pi/6) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(5*pi/12)  =  sin(pi/12),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : (-sin(pi/12)) ** 4 = (sin(pi/12)**2)**2,
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
  rw tan_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_4_308_RMHT (h0 : cos(5*pi/12) ≠ 0) : (tan(5*pi/12) + 1)/(1 - tan(5*pi/12))=-sqrt(3):=
begin
  rw tan_eq_sin_div_cos,
  have : sin(5*pi/12)/cos(5*pi/12) + 1  =  (cos(5*pi/12) + sin(5*pi/12))/cos(5*pi/12),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring,
  },
  rw this,
  have : 1 - sin(5*pi/12)/cos(5*pi/12)  =  (-sin(5*pi/12) + cos(5*pi/12))/cos(5*pi/12),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring,
  },
  rw this,
  have : sin(5*pi/12)  =  cos(pi/12),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(5*pi/12) + cos(pi/12)  =  2*cos(pi/6)*cos(pi/4),
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
  have : -cos(pi/12) + cos(5*pi/12)  =  -2*sin(pi/6)*sin(pi/4),
  {
  rw neg_add_eq_sub,
  rw cos_sub_cos,
  have : sin(((5*pi/12) + (pi/12))/2) = sin (pi/4),
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
  ring,
  },
  rw this,
  rw cos_pi_div_six,
  rw cos_pi_div_four,
  rw sin_pi_div_six,
  rw sin_pi_div_four,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_4_309_BJMY (h0 : sin(pi/18)**2 + 1 ≠ 0) : (3 - sin(7*pi/18))/(2 - cos(pi/18)**2)=2:=
begin
  have : sin(7*pi/18)  =  cos(pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(pi/9)  =  -sin(pi/18)**2 + cos(pi/18)**2,
  {
  have : cos (pi/9) = cos(2*(pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  rw cos_sq',
  have : 2 - (1 - sin(π/18)**2) = sin(pi/18)**2 + 1,
  {
  ring,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_4_310_KZFP : sin(5*pi/12)**2 - 1=(sqrt(3)-2)/4:=
begin
  have : sin(5*pi/12)**2 - 1  =  sin(5*pi/12)**2 - (sin(5*pi/12)**2 + cos(5*pi/12)**2),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : cos(5*pi/12)  =  -sin(pi/6)*sin(pi/4) + cos(pi/6)*cos(pi/4),
  {
  have : cos(5*pi/12) = cos((pi/4) + (pi/6)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_add,
  ring,
  },
  rw this,
  rw cos_pi_div_four,
  rw sin_pi_div_four,
  rw sin_pi_div_six,
  rw cos_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring_exp,
  rw sq_sqrt,
  ring_exp,
  repeat {linarith},
end

lemma Trigo_4_311_AZDL (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(2*x + pi)*cos(x)**2/((cos(2*x) + 1)*cos(x + pi/2))=cos(x):=
begin
  have : sin(2*x + pi)  =  -sin(2*x),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (2*x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(2*x)  =  -sin(x)**2 + cos(x)**2,
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
  have : -(1 - cos(x)**2) + cos(x)**2 + 1 = 2*cos(x)**2,
  {
  ring,
  },
  rw this,
  have : cos(x + pi/2)  =  -sin(x),
  {
  rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(2*x)  =  2*sin(x)*cos(x),
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
  field_simp,
  ring_exp,
end

lemma Trigo_4_312_PTCV : sin(pi/6)*sin(5*pi/12) + cos(pi/6)*cos(5*pi/12)=sqrt(2)/2:=
begin
  rw add_comm,
  have : cos(pi/6)*cos(5*pi/12) + sin(pi/6)*sin(5*pi/12)  =  cos(-pi/4),
  {
  have : cos(-pi/4) = cos((pi/6) - (5*pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_sub,
  },
  rw this,
  have : cos(-pi/4)  =  cos(pi/4),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/4) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_four,
end

lemma Trigo_4_313_DPDC : (sin(pi/12) + cos(pi/12))/(-sin(pi/12) + cos(pi/12))=sqrt(3):=
begin
  have : sin(pi/12)  =  cos(5*pi/12),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(5*pi/12) + cos(pi/12)  =  2*cos(pi/6)*cos(pi/4),
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
  have : cos(pi/4)  =  sin(pi/4),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/4) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(5*pi/12)  =  sin(pi/12),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(pi/12)  =  sin(5*pi/12),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw ← sub_eq_neg_add,
  have : sin(5*pi/12) - sin(pi/12)  =  2*sin(pi/6)*cos(pi/4),
  {
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
  rw sin_pi_div_four,
  rw cos_pi_div_six,
  rw sin_pi_div_six,
  rw cos_pi_div_four,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_4_314_PHSV : sin(13*pi/90)*sin(17*pi/90) - cos(13*pi/90)*cos(17*pi/90)=-1/2:=
begin
  rw sub_eq_neg_add,
  rw ← neg_mul,
  have : -cos(13*pi/90)*cos(17*pi/90) + sin(13*pi/90)*sin(17*pi/90)  =  -cos(pi/3),
  {
  have : cos(pi/3) = -sin(13*pi/90)*sin(17*pi/90) + cos(13*pi/90)*cos(17*pi/90),
  {
  have : cos(pi/3) = cos((13*pi/90) + (17*pi/90)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_add,
  ring,
  },
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  norm_num,
end

lemma Trigo_4_315_JZKD (h0 : cos(5*pi/18) ≠ 0) (h1 : sin(2*pi/9) ≠ 0) : (-sqrt(3)*tan(5*pi/18) + 1)*cos(pi/9)=-1:=
begin
  rw tan_eq_sin_div_cos,
  have : -sqrt(3)*(sin(5*pi/18)/cos(5*pi/18)) + 1  =  (-sqrt(3)*sin(5*pi/18) + cos(5*pi/18))/cos(5*pi/18),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : -sqrt(3)*sin(5*pi/18)  =  -2*sin(5*pi/18)*sin(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(5*pi/18)  =  2*cos(5*pi/18)*cos(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : -2*sin(5*pi/18)*sin(pi/3) + 2*cos(5*pi/18)*cos(pi/3)  =  2*cos(11*pi/18),
  {
  have : cos(11*pi/18) = -sin(5*pi/18)*sin(pi/3) + cos(5*pi/18)*cos(pi/3),
  {
  have : cos(11*pi/18) = cos((pi/3) + (5*pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_add,
  ring,
  },
  linarith,
  },
  rw this,
  have : cos(11*pi/18)  =  -sin(pi/9),
  {
  rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (11*pi/18) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_assoc,
  have : cos(5*pi/18)*cos(pi/3)  =  cos(5*pi/18)/2,
  {
  field_simp,
  },
  rw this,
  have : cos(5*pi/18)  =  sin(2*pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : 2*-sin(π/9)/(2*(sin(2*π/9)/2))*cos(π/9) = -2*sin(pi/9)*cos(pi/9)/(2*(sin(2*π/9)/2)),
  {
  ring,
  },
  rw this,
  have : -2*sin(pi/9)*cos(pi/9)  =  -sin(2*pi/9),
  {
  have : sin(2*pi/9) = 2*sin(pi/9)*cos(pi/9),
  {
  have : sin (2*pi/9) = sin(2*(pi/9)),
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
  field_simp,
  ring_exp,
end

lemma Trigo_4_316_QHYQ (h0 : 2 ≠ 0) (h1 : sin(x) + cos(x) ≠ 0) : sin(x + pi/4)/(2*sin(x/2)*cos(x/2) + 2*cos(x/2)**2 - 1)=sqrt(2)/2:=
begin
  have : sin(x + pi/4)  =  sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
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
  have : 2*sin(x/2)*cos(x/2)  =  sin(x),
  {
  have : sin (x) = sin(2*(x/2)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : sin(x) + 2*cos(x/2)**2 - 1  = sin(x) + cos(x/2)**2 -sin(x/2)**2,
  {
  have : sin(x) + 2*cos(x/2)**2 - 1 = sin(x) + 2*cos(x/2)**2 - (sin(x/2)**2 + cos(x/2)**2),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  ring,
  },
  rw this,
  rw ← sub_add_eq_add_sub,
  rw sub_eq_add_neg,
  rw add_assoc,
  have : -sin(x/2)**2 + cos(x/2)**2  =  cos(x),
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
  rw cos_pi_div_four,
  rw sin_pi_div_four,
  field_simp,
  ring_exp,
end

lemma Trigo_4_317_CRBD (h0 : sin(3) - cos(3) ≥ 0) : sqrt(2*sin(-3 + pi)*cos(-3 + pi) + 1)=sin(3)-cos(3):=
begin
  have : sin(-3 + pi)  =  sin(3),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-3 + pi) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-3 + pi)  =  -cos(3),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-3 + pi) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : 2*sin(3)*-cos(3) + 1 = -2*sin(3)*cos(3) + (sin(3)**2  + cos(3)**2),
  {
  rw sin_sq_add_cos_sq,
  ring,
  },
  rw this,
  have : -2*sin(3)*cos(3) + (sin(3)**2 + cos(3)**2)  =  (sin(3) - cos(3))**2,
  {
  ring_exp,
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h0,
end

lemma Trigo_4_318_OXCR (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(pi - x)*cos(-x + 2*pi)*tan(-x - pi)*tan(-x + 3*pi/2)/sin(-x - pi)=-cos(x):=
begin
  have : sin(pi - x)  =  sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-x + 2*pi)  =  cos(x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : tan(-x - pi)  =  -tan(x + pi),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - pi) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(x + pi)  =  tan(x),
  {
  rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : tan(-x + 3*pi/2)  =  1/tan(x),
  {
  rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-x + 3*pi/2) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-x - pi)  =  sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_4_319_WRXS (h0 : cos(pi/18) ≠ 0) : (-tan(pi/18) + sqrt(3))*cos(5*pi/18)=1:=
begin
  rw tan_eq_sin_div_cos,
  have : -(sin(pi/18)/cos(pi/18)) + sqrt(3)  =  (-sin(pi/18) + sqrt(3)*cos(pi/18))/cos(pi/18),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : sqrt(3)*cos(pi/18)  =  2*sin(pi/3)*cos(pi/18),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : sin(pi/18)  =  2*sin(pi/18)*cos(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  rw ← neg_mul,
  rw ← neg_mul,
  have : -2*sin(pi/18)*cos(pi/3) + 2*sin(pi/3)*cos(pi/18)  =  2*sin(5*pi/18),
  {
  have : sin(5*pi/18) = -sin(pi/18)*cos(pi/3) + sin(pi/3)*cos(pi/18),
  {
  have : sin(5*pi/18) = sin((pi/3) - (pi/18)),
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
  rw div_mul_eq_mul_div,
  have : 2*sin(5*pi/18)*cos(5*pi/18)  =  sin(5*pi/9),
  {
  have : sin (5*pi/9) = sin(2*(5*pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : sin(5*pi/9)  =  cos(pi/18),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
end

lemma Trigo_4_320_QBWT : sin(-pi/10)**2 - sin(-pi/10)*cos(4*pi/15) + cos(4*pi/15)**2=3/4:=
begin
  have : sin(-pi/10)**2  =  1/2 - cos(-pi/5)/2,
  {
  have : cos (-pi/5) = cos(2*(-pi/10)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(4*pi/15)**2  =  1/2 + cos(8*pi/15)/2,
  {
  have : cos (8*pi/15) = cos(2*(4*pi/15)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  have : cos(-pi/5)  =  cos(pi/5),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/5) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : 1/2 - cos(π/5)/2 - sin(-π/10)*cos(4*π/15) + (1/2 + cos(8*π/15)/2) = cos(8*pi/15)/2 - cos(pi/5)/2 - sin(-π/10)*cos(4*π/15) + 1,
  {
  ring,
  },
  rw this,
  have : cos(8*pi/15)/2 - cos(pi/5)/2  =  -sin(11*pi/30)*sin(pi/6),
  {
  have : -cos(pi/5) + cos(8*pi/15) = -2*sin(pi/6)*sin(11*pi/30),
  {
  rw neg_add_eq_sub,
  rw cos_sub_cos,
  have : sin(((8*pi/15) + (pi/5))/2) = sin (11*pi/30),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((8*pi/15) - (pi/5))/2) = sin(pi/6),
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
  have : sin(-pi/10)*cos(4*pi/15)  =  -sin(11*pi/30)/2 + sin(pi/6)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((4*pi/15) + (-pi/10)) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((4*pi/15) - (-pi/10)) = sin (11*pi/30),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_4_321_RNEK : sin(pi/6)*cos(pi/12) + cos(pi/6)*cos(5*pi/12)=sqrt(2)/2:=
begin
  have : cos(5*pi/12)  =  sin(pi/12),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw add_comm,
  rw mul_comm (cos(pi/6)) (sin(pi/12)),
  have : sin(pi/12)*cos(pi/6) + sin(pi/6)*cos(pi/12)  =  sin(pi/4),
  {
  have : sin(pi/4) = sin((pi/6) + (pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
  },
  rw this,
  rw sin_pi_div_four,
end

lemma Trigo_4_322_RFNH : sin(4*pi/9)*cos(11*pi/36) + cos(7*pi/36)*cos(4*pi/9)=sqrt(2)/2:=
begin
  have : cos(11*pi/36)  =  sin(7*pi/36),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw add_comm,
  rw mul_comm (sin(4*pi/9)) (sin(7*pi/36)),
  have : cos(7*pi/36)*cos(4*pi/9) + sin(7*pi/36)*sin(4*pi/9)  =  cos(pi/4),
  {
  have : cos(pi/4) = cos((4*pi/9) - (7*pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_sub,
  ring,
  },
  rw this,
  rw cos_pi_div_four,
end

lemma Trigo_4_323_UTUG (h0 : cos(4) - sin(4) ≥ 0) : sqrt(1 - sin(8))=cos(4)-sin(4):=
begin
  have : 1 - sin(8)  =  cos(4)**2 + sin(4)**2 - sin(8),
  {
  rw cos_sq_add_sin_sq,
  },
  rw this,
  have : sin(8)  =  2*sin(4)*cos(4),
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
  have : cos(4)**2 + sin(4)**2 - 2*sin(4)*cos(4)  =  (cos(4) - sin(4))**2,
  {
  ring_exp,
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h0,
end

lemma Trigo_4_324_UJQY (h0 : cos(pi/18) ≠ 0) (h1 : sin(5*pi/18) ≠ 0) : (tan(pi/18) - sqrt(3))*cos(pi/18)/sin(5*pi/18)=-2:=
begin
  rw tan_eq_sin_div_cos,
  have : sin(pi/18)/cos(pi/18) - sqrt(3)  =  (-sqrt(3)*cos(pi/18) + sin(pi/18))/cos(pi/18),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring,
  },
  rw this,
  have : -sqrt(3)*cos(pi/18)  =  -2*cos(pi/18)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : sin(pi/18)  =  2*sin(pi/18)*sin(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : -2*cos(pi/18)*cos(pi/6) + 2*sin(pi/18)*sin(pi/6)  =  -2*cos(2*pi/9),
  {
  have : cos(2*pi/9) = -sin(pi/18)*sin(pi/6) + cos(pi/18)*cos(pi/6),
  {
  have : cos(2*pi/9) = cos((pi/6) + (pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_add,
  ring,
  },
  linarith,
  },
  rw this,
  have : cos(2*pi/9)  =  -sin(-5*pi/18),
  {
  rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (2*pi/9) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-5*pi/18)  =  -sin(5*pi/18),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_4_325_DUZH (h0 : cos(3*pi/20) ≠ 0) (h1 : cos(pi/60) ≠ 0) (h2 : 1 - tan(pi/60) * tan(3*pi/20) ≠ 0) : tan(pi/60)*tan(3*pi/20) + tan(pi/60)*tan(pi/3) + tan(3*pi/20)*tan(pi/3)=1:=
begin
  rw add_assoc,
  have : tan(pi/60)*tan(pi/3) + tan(3*pi/20)*tan(pi/3)  =  (tan(pi/60) + tan(3*pi/20))*tan(pi/3),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_three, -cos_pi_div_three, -sin_pi_div_two, -cos_pi_div_two],
  ring_exp,
  },
  rw this,
  have : tan(pi/60) + tan(3*pi/20)  =  (-tan(pi/60)*tan(3*pi/20) + 1)*tan(pi/6),
  {
  rw tan_add_tan,
  have : tan((pi/60) + (3*pi/20)) = tan (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(pi/60)*tan(3*pi/20) + 1)*tan(pi/6)  =  -tan(pi/60)*tan(3*pi/20)*tan(pi/6) + tan(pi/6),
  {
  ring_exp,
  },
  rw this,
  have : (-tan(pi/60)*tan(3*pi/20)*tan(pi/6) + tan(pi/6))*tan(pi/3)  =  -tan(pi/60)*tan(3*pi/20)*tan(pi/6)*tan(pi/3) + tan(pi/6)*tan(pi/3),
  {
  ring_exp,
  },
  rw this,
  rw tan_pi_div_six,
  rw tan_pi_div_three,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_4_326_TRVW (h0 : 3 - sin(pi/18) ≠ 0) : (3 - sin(17*pi/18))/(sin(2*pi/9)**2 + 1)=2:=
begin
  have : sin(17*pi/18)  =  sin(pi/18),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(2*pi/9)**2  =  1/2 - cos(4*pi/9)/2,
  {
  have : cos (4*pi/9) = cos(2*(2*pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(4*pi/9)  =  sin(pi/18),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : 1/2 - sin(π/18)/2 + 1 = (3 - sin(pi/18))/2,
  {
  ring,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_4_327_DOGX (h0 : cos(pi/9) ≥ 0) (h1 : -cos(pi/9) + sin(pi/9) ≤ 0) : sqrt(1 - sin(8*pi/9)**2) + sqrt(-2*sin(10*pi/9)*cos(10*pi/9) + 1)=2*cos(pi/9)-sin(pi/9):=
begin
  have : sin(10*pi/9)  =  -sin(pi/9),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (10*pi/9) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(10*pi/9)  =  -cos(pi/9),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (10*pi/9) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(8*pi/9)  =  sin(pi/9),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (8*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw ← cos_sq',
  have : -2*-sin(π/9)*-cos(π/9) + 1 = -2*sin(pi/9)*cos(pi/9) + (sin(pi/9)**2 + cos(pi/9)**2),
  {
  rw sin_sq_add_cos_sq,
  ring,
  },
  rw this,
  have : -2*sin(pi/9)*cos(pi/9) + (sin(pi/9)**2 + cos(pi/9)**2)  =  (-cos(pi/9) + sin(pi/9))**2,
  {
  ring_exp,
  },
  rw this,
  repeat {rw sqrt_sq_eq_abs},
  rw abs_eq_self.mpr h0,
  rw abs_eq_neg_self.mpr h1,
  norm_num,
  ring_exp,
end

lemma Trigo_4_328_IZYH (h0 : 1 - tan(pi/18) * tan(5*pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : cos(5*pi/18) ≠ 0) (h3 : tan(pi/18) ≠ 0) (h4 : tan(5*pi/18) ≠ 0) : (tan(pi/18) + tan(5*pi/18) + tan(2*pi/3))/(tan(pi/18)*tan(5*pi/18))=-sqrt(3):=
begin
  have : tan(2*pi/3)  =  -tan(pi/3),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(pi/18) + tan(5*pi/18)  =  (-tan(pi/18)*tan(5*pi/18) + 1)*tan(pi/3),
  {
  rw tan_add_tan,
  have : tan((pi/18) + (5*pi/18)) = tan (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(pi/18)*tan(5*pi/18) + 1)*tan(pi/3)  =  -tan(pi/18)*tan(5*pi/18)*tan(pi/3) + tan(pi/3),
  {
  ring_exp,
  },
  rw this,
  rw tan_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_4_329_APFG : sin(pi/10)**2 - sin(pi/10)*cos(pi/15) + cos(pi/15)**2=3/4:=
begin
  have : sin(pi/10)*cos(pi/15)  =  sin(pi/6)/2 + sin(pi/30)/2,
  {
  rw sin_mul_cos,
  have : sin((pi/10) + (pi/15)) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((pi/10) - (pi/15)) = sin (pi/30),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(pi/10)**2  =  1/2 - cos(pi/5)/2,
  {
  have : cos (pi/5) = cos(2*(pi/10)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(pi/15)**2  =  1/2 + cos(2*pi/15)/2,
  {
  have : cos (2*pi/15) = cos(2*(pi/15)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  have : 1/2 - cos(π/5)/2 - (sin(π/6)/2 + sin(π/30)/2) + (1/2 + cos(2*π/15)/2) = -cos(pi/5)/2 + cos(2*pi/15)/2 - (sin(π/6)/2 + sin(π/30)/2) + 1,
  {
  ring,
  },
  rw this,
  have : -cos(pi/5)/2 + cos(2*pi/15)/2  =  sin(pi/30)*sin(pi/6),
  {
  have : -cos(2*pi/15) + cos(pi/5) = -2*sin(pi/30)*sin(pi/6),
  {
  rw neg_add_eq_sub,
  rw cos_sub_cos,
  have : sin(((pi/5) + (2*pi/15))/2) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((pi/5) - (2*pi/15))/2) = sin(pi/30),
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
  rw sin_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_4_330_QHIH (h0 : sin(pi/9) ≠ 0) : sin(pi/18)*sin(5*pi/18)*sin(7*pi/18)=1/8:=
begin
  have : sin(pi/18)  =  cos(4*pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(5*pi/18)  =  cos(2*pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(7*pi/18)  =  cos(pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(pi/9)  =  sin(2*pi/9)/(2*sin(pi/9)),
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
  have : cos(4*π/9)*cos(2*π/9)*(sin(2*π/9)/(2*sin(π/9))) = sin(2*π/9)*cos(2*π/9)*cos(4*π/9)/(2*sin(π/9)),
  {
  ring,
  },
  rw this,
  have : sin(2*pi/9)*cos(2*pi/9)  =  sin(4*pi/9)/2,
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
  have : sin(4*π/9)/2*cos(4*π/9)/(2*sin(π/9)) = sin(4*π/9)*cos(4*π/9)/2/(2*sin(π/9)),
  {
  ring_exp,
  },
  rw this,
  have : sin(4*pi/9)*cos(4*pi/9)  =  sin(8*pi/9)/2,
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
  have : sin(8*pi/9)  =  sin(pi/9),
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

lemma Trigo_4_331_NSKW (h0 : 2 ≠ 0) (h1 : 2*sin(x)*cos(x) + 2*cos(x)**2 ≠ 0) (h2 : cos(x) ≠ 0) : (sin(2*x) + 1)/(sin(2*x) + 2*cos(x)**2)=1/2*tan(x)+1/2:=
begin
  have : sin(2*x)  =  2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_two_mul,
  },
  rw this,
  have : 2*sin(x)*cos(x) + 1 = 2*sin(x)*cos(x) + (sin(x)**2 + cos(x)**2),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : 2*sin(x)*cos(x) + (sin(x)**2 + cos(x)**2)  =  (sin(x) + cos(x))**2,
  {
  ring_exp,
  },
  rw this,
  have : (sin(x) + cos(x))**2/(2*sin(x)*cos(x) + 2*cos(x)**2)  =  (sin(x) + cos(x))/(2*cos(x)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  field_simp,
  ring_exp,
end

lemma Trigo_4_332_DYHV (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(pi - x)*sin(x + 3*pi/2)*cos(-x + 2*pi)*tan(-x - pi)/(sin(x - pi)*cos(x + pi/2))=cos(x):=
begin
  have : sin(pi - x)  =  sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(x + 3*pi/2)  =  -cos(x),
  {
  rw sin_eq_neg_cos_add_pi_div_two_add_int_mul_two_pi (x + 3*pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-x + 2*pi)  =  cos(x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : tan(-x - pi)  =  -tan(x),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(x - pi)  =  -sin(pi - x),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (x - pi) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(pi - x)  =  sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(x + pi/2)  =  -sin(x),
  {
  rw cos_eq_neg_sin_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_4_333_RAEI (h0 : cos(pi/18) ≠ 0) : (sqrt(3)*tan(pi/18) + 1)*sin(5*pi/18)=1:=
begin
  rw tan_eq_sin_div_cos,
  have : sqrt(3)*(sin(pi/18)/cos(pi/18)) + 1  =  (sqrt(3)*sin(pi/18) + cos(pi/18))/cos(pi/18),
  {
  ring_exp,
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : sqrt(3)*sin(pi/18)  =  2*sin(pi/18)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/18)  =  2*sin(pi/6)*cos(pi/18),
  {
  field_simp,
  },
  rw this,
  have : 2*sin(pi/18)*cos(pi/6) + 2*sin(pi/6)*cos(pi/18)  =  2*sin(2*pi/9),
  {
  have : sin(2*pi/9) = sin(pi/18)*cos(pi/6) + sin(pi/6)*cos(pi/18),
  {
  have : sin(2*pi/9) = sin((pi/6) + (pi/18)),
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
  have : sin(5*pi/18)  =  cos(2*pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : 2*sin(2*π/9)/(2*(1/2)*cos(π/18))*cos(2*π/9) = 2*sin(2*pi/9)*cos(2*pi/9)/(2*(1/2)*cos(π/18)),
  {
  ring,
  },
  rw this,
  have : 2*sin(2*pi/9)*cos(2*pi/9)  =  sin(4*pi/9),
  {
  have : sin (4*pi/9) = sin(2*(2*pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : sin(4*pi/9)  =  cos(pi/18),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
end

lemma Trigo_4_334_CJGK (h0 : cos(x - y) ≠ 0) (h1 : cos(x + y) ≠ 0) : tan(x - y) + tan(x + y)=sin(2*x)/(cos(x)**2-sin(y)**2):=
begin
  rw tan_eq_sin_div_cos,
  rw tan_eq_sin_div_cos,
  have : sin(x - y)/cos(x - y) + sin(x + y)/cos(x + y)  =  (sin(x - y)*cos(x + y) + sin(x + y)*cos(x - y))/(cos(x - y)*cos(x + y)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : sin(x - y)*cos(x + y) + sin(x + y)*cos(x - y)  =  sin(2*x),
  {
  have : sin(2*x) = sin((x + y) + (x - y)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add (x+y) (x-y),
  ring,
  },
  rw this,
  have : cos(x - y)  =  sin(x)*sin(y) + cos(x)*cos(y),
  {
  have : cos(x-y) = cos((x) - (y)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_sub,
  ring,
  },
  rw this,
  have : cos(x + y)  =  -sin(x)*sin(y) + cos(x)*cos(y),
  {
  have : cos(x+y) = cos((x) + (y)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_add,
  ring,
  },
  rw this,
  have : (sin(x)*sin(y) + cos(x)*cos(y))*(-sin(x)*sin(y) + cos(x)*cos(y)) = -sin(x)**2*sin(y)**2 + cos(x)**2*cos(y)**2,
  {
  ring_exp,
  },
  rw this,
  rw cos_sq' y,
  rw sin_sq x,
  have : -(1 - cos(x)**2)*sin(y)**2 + cos(x)**2*(1 - sin(y)**2) = cos x ** 2 - sin y ** 2,
  {
  ring_exp,
  },
  rw this,
end

lemma Trigo_4_335_JVWS (h0 : 1 - tan(5*pi/36) * tan(7*pi/36) ≠ 0) (h1 : cos(5*pi/36) ≠ 0) (h2 : cos(7*pi/36) ≠ 0) : sqrt(3)*tan(5*pi/36)*tan(7*pi/36) + tan(5*pi/36) + tan(7*pi/36)=sqrt(3):=
begin
  rw add_assoc,
  have : tan(5*pi/36) + tan(7*pi/36)  =  (-tan(5*pi/36)*tan(7*pi/36) + 1)*tan(pi/3),
  {
  rw tan_add_tan,
  have : tan((5*pi/36) + (7*pi/36)) = tan (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(5*pi/36)*tan(7*pi/36) + 1)*tan(pi/3)  =  -tan(5*pi/36)*tan(7*pi/36)*tan(pi/3) + tan(pi/3),
  {
  ring_exp,
  },
  rw this,
  rw tan_pi_div_three,
  ring_exp,
end

lemma Trigo_4_336_BNFJ : sin(pi/8)**2 - cos(pi/8)**2=-sqrt(2)/2:=
begin
  rw sub_eq_neg_add,
  have : -cos(pi/8)**2 + sin(pi/8)**2  =  -cos(pi/4),
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
  ring_exp,
end


lemma Trigo_4_337_VMBT (h0 : cos(pi/18) ≠ 0) : (tan(pi/18) - sqrt(3))*sin(2*pi/9)=-1:=
begin
  rw tan_eq_sin_div_cos,
  have : sin(pi/18)/cos(pi/18) - sqrt(3) =  (-sqrt(3)*cos(pi/18) + sin(pi/18))/cos(pi/18),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw neg_mul,
  have : sqrt(3)*cos(pi/18)  =  2*sin(pi/3)*cos(pi/18),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : sin(pi/18)  =  2*sin(pi/18)*cos(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  rw ← neg_mul,
  rw ← neg_mul,
  have : -2*sin(pi/3)*cos(pi/18) + 2*sin(pi/18)*cos(pi/3)  =  2*sin(-5*pi/18),
  {
  have : sin(-5*pi/18) = sin(pi/18)*cos(pi/3) - sin(pi/3)*cos(pi/18),
  {
  have : sin(-5*pi/18) = sin((pi/18) - (pi/3)),
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
  have : sin(-5*pi/18)  =  -sin(5*pi/18),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : 2*-sin(5*π/18)/cos(π/18)*sin(2*π/9) = -2*(sin(2*pi/9)*sin(5*pi/18))/cos(π/18),
  {
  ring,
  },
  rw this,
  have : sin(2*pi/9)*sin(5*pi/18)  =  -cos(pi/2)/2 + cos(-pi/18)/2,
  {
  rw sin_mul_sin,
  have : cos((2*pi/9) + (5*pi/18)) = cos (pi/2),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((2*pi/9) - (5*pi/18)) = cos (-pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : cos(-pi/18)  =  cos(pi/18),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_two,
  norm_num,
  field_simp,
end

lemma Trigo_4_338_BJHZ : 2*sin(1)**2 + 2*cos(1)**2=2:=
begin
  have : sin(1)**2 + cos(1)**2 = 1,
  {
  rw sin_sq_add_cos_sq,
  },
  linarith,
end

lemma Trigo_4_339_LVRV (h0 : sin(5*pi/18) ≠ 0) (h1 : cos(5*pi/18) ≠ 0) (h2 : cos(pi/18) ≠ 0) : sqrt(3)/cos(5*pi/18) + 1/sin(5*pi/18)=4:=
begin
  have : sqrt(3)/cos(5*pi/18) + 1/sin(5*pi/18)  =  (cos(5*pi/18) + sqrt(3)*sin(5*pi/18))/(sin(5*pi/18)*cos(5*pi/18)),
  {
  ring_exp,
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : cos(5*pi/18) + sqrt(3)*sin(5*pi/18)  =  2*sin(pi/6)*cos(5*pi/18) + 2*sin(5*pi/18)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : 2*sin(pi/6)*cos(5*pi/18) + 2*sin(5*pi/18)*cos(pi/6)  =  2*sin(4*pi/9),
  {
  have : sin(4*pi/9) = sin(pi/6)*cos(5*pi/18) + sin(5*pi/18)*cos(pi/6),
  {
  have : sin(4*pi/9) = sin((pi/6) + (5*pi/18)),
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
  have : sin(5*pi/18)*cos(5*pi/18) = sin(5*pi/9)/2,
  {
  have : sin(5*pi/9) = 2*sin(5*pi/18)*cos(5*pi/18),
  {
  have : sin (5*pi/9) = sin(2*(5*pi/18)),
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
  have : sin(4*pi/9)  =  cos(pi/18),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(5*pi/9)  =  cos(pi/18),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_4_340_JESM (h0 : cos(2*x) ≠ 0) (h1 : sin(2*x) + cos(2*x) ≠ 0) : (sin(4*x) - cos(4*x) + 1)/(sin(4*x) + cos(4*x) + 1)=tan(2*x):=
begin
  have : cos(4*x)  =  -sin(2*x)**2 + cos(2*x)**2,
  {
  have : cos (4*x) = cos(2*(2*x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : sin(4*x) - (-sin(2*x)**2 + cos(2*x)**2) + 1 = sin(4*x) - (-sin(2*x)**2 + cos(2*x)**2) + (sin(2*x)**2 + cos(2*x)**2),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : sin(4*x) - (-sin(2*x)**2 + cos(2*x)**2) + (sin(2*x)**2 + cos(2*x)**2) = sin(4*x) + 2*sin(2*x)**2,
  {
  ring,
  },
  rw this,
  have : sin(4*x) + (-sin(2*x)**2 + cos(2*x)**2) + 1 = sin(4*x) + (-sin(2*x)**2 + cos(2*x)**2) + (sin(2*x)**2 + cos(2*x)**2),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : sin(4*x) + (-sin(2*x)**2 + cos(2*x)**2) + (sin(2*x)**2 + cos(2*x)**2) = sin(4*x) + 2*cos(2*x)**2,
  {
  ring,
  },
  rw this,
  have : sin(4*x)  =  2*sin(2*x)*cos(2*x),
  {
  have : sin (4*x) = sin(2*(2*x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : 2*sin(2*x)*cos(2*x) + 2*sin(2*x)**2  =  2*sin(2*x)*(sin(2*x) + cos(2*x)),
  {
  ring_exp,
  },
  rw this,
  have : 2*sin(2*x)*cos(2*x) + 2*cos(2*x)**2  =  2*cos(2*x)*(sin(2*x) + cos(2*x)),
  {
  ring_exp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  field_simp,
  ring_exp,
end

lemma Trigo_4_341_YKKV (h0 : cos(x) ≠ 0) (h1 : sin(x) ≠ 0) : sin(-x + 2*pi)*cos(x - 7*pi/2)/(sin(x + 3*pi/2)*cos(x + 2*pi)) + tan(-x + 3*pi)/(sin(pi - x)*sin(-x + 3*pi/2))=1:=
begin
  have : sin(-x + 2*pi)  =  -sin(x),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(x - 7*pi/2)  =  cos(-x + 7*pi/2),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (x - 7*pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-x + 7*pi/2)  =  -cos(-x + pi/2),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-x + 7*pi/2) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-x + pi/2)  =  sin(x),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-x + pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(x + 3*pi/2)  =  -sin(x + pi/2),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + 3*pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(x + pi/2)  =  cos(x),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(x + 2*pi)  =  cos(x),
  {
  rw cos_eq_cos_add_int_mul_two_pi (x + 2*pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : tan(-x + 3*pi)  =  -tan(x),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-x + 3*pi) (3),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(pi - x)  =  sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : sin(-x + 3*pi/2)  =  -sin(-x + pi/2),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-x + 3*pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-x + pi/2)  =  cos(x),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-x + pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  have : -sin(x)*-sin(x)/(-cos(x)*cos(x)) + -(sin(x)/cos(x))/(sin(x)*-cos(x))  =  (1 - sin(x)**2)/cos(x)**2,
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw sin_sq,
  norm_num,
  field_simp,
end

lemma Trigo_4_342_JEBY : sin(pi/4)*cos(pi/12) - sin(11*pi/12)*cos(pi/4)=1/2:=
begin
  have : sin(11*pi/12)  =  sin(pi/12),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (11*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sub_eq_neg_add,
  rw ← neg_mul,
  have : -sin(pi/12)*cos(pi/4) + sin(pi/4)*cos(pi/12)  =  sin(pi/6),
  {
  have : sin(pi/6) = sin((pi/4) - (pi/12)),
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

lemma Trigo_4_343_QYWS (h0 : sin(x) ≠ 0) : (1 - cos(x))*(1/tan(x) + 1/sin(x))=sin(x):=
begin
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  have : cos(x)/sin(x) + 1/sin(x)  =  (cos(x) + 1)/sin(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  rw mul_div_assoc',
  have : (1 - cos(x))*(cos(x) + 1)  =  1 - cos(x)**2,
  {
  ring_exp,
  },
  rw this,
  rw ← sin_sq,
  field_simp,
  ring_exp,
end

lemma Trigo_4_344_QPKD (h0 : sin(pi/15) ≠ 0) : sin(pi/30)*sin(13*pi/30)*cos(2*pi/15)*cos(4*pi/15)=1/16:=
begin
  have : sin(pi/30)  =  cos(7*pi/15),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/30) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(13*pi/30)  =  cos(pi/15),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (13*pi/30) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(pi/15)  =  sin(2*pi/15)/(2*sin(pi/15)),
  {
  have : sin (2*pi/15) = sin(2*(pi/15)),
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
  have : cos(7*π/15)*(sin(2*π/15)/(2*sin(π/15)))*cos(2*π/15)*cos(4*π/15) = sin(2*π/15)*cos(2*π/15)*cos(4*π/15)*cos(7*π/15)/(2*sin(π/15)),
  {
  ring,
  },
  rw this,
  have : sin(2*pi/15)*cos(2*pi/15)  =  sin(4*pi/15)/2,
  {
  have : sin(4*pi/15) = 2*sin(2*pi/15)*cos(2*pi/15),
  {
  have : sin (4*pi/15) = sin(2*(2*pi/15)),
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
  have : sin(4*π/15)/2*cos(4*π/15) = sin(4*π/15)*cos(4*π/15)/2,
  {
  ring,
  },
  rw this,
  have : sin(4*pi/15)*cos(4*pi/15)  =  sin(8*pi/15)/2,
  {
  have : sin(8*pi/15) = 2*sin(4*pi/15)*cos(4*pi/15),
  {
  have : sin (8*pi/15) = sin(2*(4*pi/15)),
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
  have : cos(7*pi/15)  =  -cos(8*pi/15),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (7*pi/15) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(8*π/15)/2/2*-cos(8*π/15) = -(sin(8*π/15)*cos(8*π/15)/2/2),
  {
  ring,
  },
  rw this,
  have : sin(8*pi/15)*cos(8*pi/15)  =  sin(16*pi/15)/2,
  {
  have : sin(16*pi/15) = 2*sin(8*pi/15)*cos(8*pi/15),
  {
  have : sin (16*pi/15) = sin(2*(8*pi/15)),
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
  have : sin(16*pi/15)  =  -sin(pi/15),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (16*pi/15) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_4_345_DSOO : sin(31*pi/36)*cos(7*pi/36) - cos(5*pi/36)*cos(47*pi/36)=sqrt(3)/2:=
begin
  have : sin(31*pi/36)  =  sin(5*pi/36),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (31*pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(47*pi/36)  =  -cos(11*pi/36),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (47*pi/36) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(11*pi/36)  =  sin(7*pi/36),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_neg,
  rw sub_eq_add_neg,
  rw neg_neg,
  rw mul_comm (cos(5*pi/36)) (sin(7*pi/36)),
  have : sin(5*pi/36)*cos(7*pi/36) + sin(7*pi/36)*cos(5*pi/36)  =  sin(pi/3),
  {
  have : sin(pi/3) = sin((5*pi/36) + (7*pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
  },
  rw this,
  rw sin_pi_div_three,
end

lemma Trigo_4_346_HJNU (h0 : cos(19*pi/180) ≠ 0) (h1 : cos(11*pi/180) ≠ 0) (h2 : 1-tan(11*pi/180)*tan(19*pi/180) ≠ 0) (h3 : tan((11*pi/180)+(19*pi/180)) ≠ 0) : tan(11*pi/180)*tan(19*pi/180) + sqrt(3)*tan(11*pi/180) + sqrt(3)*tan(19*pi/180)=1:=
begin
  have : tan(11*pi/180)*tan(19*pi/180)  =  -(tan(11*pi/180) + tan(19*pi/180))/tan(pi/6) + 1,
  {
  rw tan_mul_tan',
  have : tan((11*pi/180) + (19*pi/180)) = tan (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  repeat {assumption},
  },
  rw this,
  rw tan_pi_div_six,
  rw sqrt_div_self,
  field_simp,
  ring_exp,
end

lemma Trigo_4_347_ZWTX (h0 : 1 - tan(x/2) ≠ 0) (h1 : cos(pi/4) ≠ 0) (h2 : cos(x/2) ≠ 0) (h3 : 1 + tan(x/2) ≠ 0) (h3 : tan(x/2) + 1 ≠ 0) (h4 : -tan(x/2) + 1 ≠ 0) : tan(x/2 - pi/4) + tan(x/2 + pi/4)=2*tan(x):=
begin
  have : tan(x/2 - pi/4)  =  (tan(x/2) - tan(pi/4))/(tan(pi/4)*tan(x/2) + 1),
  {
  have : tan(x/2 - pi/4) = tan((x/2) - (pi/4)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw tan_sub,
  field_simp,
  left,
  ring_exp,
  repeat {assumption},
  },
  rw this,
  have : tan(x/2 + pi/4)  =  (tan(x/2) + tan(pi/4))/(-tan(pi/4)*tan(x/2) + 1),
  {
  have : tan(x/2 + pi/4) = tan((x/2) + (pi/4)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw tan_add,
  field_simp,
  left,
  ring_exp,
  repeat {assumption},
  },
  rw this,
  rw tan_pi_div_four,
  have : (tan(x/2) - 1)/(1*tan(x/2) + 1) + (tan(x/2) + 1)/(-1*tan(x/2) + 1)  =  ((1 - tan(x/2))*(tan(x/2) - 1) + (tan(x/2) + 1)**2)/((1 - tan(x/2))*(tan(x/2) + 1)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : (1 - tan(x/2))*(tan(x/2) - 1)  =  -tan(x/2)**2 + 2*tan(x/2) - 1,
  {
  ring_exp,
  },
  rw this,
  have : (tan(x/2) + 1)**2  =  tan(x/2)**2 + 2*tan(x/2) + 1,
  {
  ring_exp,
  },
  rw this,
  have : (1 - tan(x/2))*(tan(x/2) + 1)  =  1 - tan(x/2)**2,
  {
  ring_exp,
  },
  rw this,
  have : (-tan(x/2)**2 + 2*tan(x/2) - 1 + (tan(x/2)**2 + 2*tan(x/2) + 1)) = 4*tan(x/2),
  {
  ring,
  },
  rw this,
  have : 4*tan(x/2)/(1 - tan(x/2)**2)  =  2*tan(x),
  {
  have : tan(x) = 2*tan(x/2)/(1 - tan(x/2)**2),
  {
  have : tan (x) = tan(2*(x/2)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw tan_two_mul,
  repeat {assumption},
  },
  rw this,
  ring_exp,
  },
  rw this,
end

lemma Trigo_4_348_WZTA (h0 : cos(7*pi/45) ≠ 0) (h1 : 1 - tan(7*pi/45) * tan(17*pi/180) ≠ 0) (h2 : cos(17*pi/180) ≠ 0) : (tan(17*pi/180) + 1)*(tan(7*pi/45) + 1)=2:=
begin
  have : (tan(17*pi/180) + 1)*(tan(7*pi/45) + 1)  =  tan(17*pi/180)*tan(7*pi/45) + tan(17*pi/180) + tan(7*pi/45) + 1,
  {
  ring_exp,
  },
  rw this,
  have : tan(17*π/180)*tan(7*π/45) + tan(17*π/180) + tan(7*π/45) + 1 = tan(17*π/180)*tan(7*π/45) + (tan(17*π/180) + tan(7*π/45)) + 1,
  {
  ring,
  },
  rw this,
  have : tan(17*pi/180) + tan(7*pi/45)  =  (-tan(17*pi/180)*tan(7*pi/45) + 1)*tan(pi/4),
  {
  rw add_comm,
  rw tan_add_tan,
  have : tan((7*pi/45) + (17*pi/180)) = tan (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  rw tan_pi_div_four,
  norm_num,
end

lemma Trigo_4_349_KYZD (h0 : cos(pi/4) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : sin(x) + cos(x) ≠ 0) (h3 : cos(2*x) ≠ 0) : (2*cos(x)**2 - 1)/(2*sin(x + pi/4)**2*tan(-x + pi/4))=1:=
begin
  have : 2*sin(x + pi/4)**2  =  1 - cos(2*x + pi/2),
  {
  have : sin(x + pi/4)**2 = 1/2 - cos(2*x + pi/2)/2,
  {
  have : cos (2*x + pi/2) = cos(2*(x + pi/4)),
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
  have : cos(2*x + pi/2)  =  -sin(pi/2)*sin(2*x) + cos(pi/2)*cos(2*x),
  {
  have : cos(2*x+pi/2) = cos((pi/2) + (2*x)),
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
  rw sin_pi_div_two,
  have : sin(2*x)  =  2*sin(x)*cos(x),
  {
  have : sin (2*x) = sin(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_two_mul,
  },
  rw this,
  simp,
  have : 1 + 2*sin(x)*cos(x) = sin(x)**2 + cos(x)**2 + 2*sin(x)*cos(x),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : sin(x)**2 + cos(x)**2 + 2*sin(x)*cos(x)  =  (sin(x) + cos(x))**2,
  {
  ring_exp,
  },
  rw this,
  have : tan(-x + pi/4)  =  (-tan(x) + tan(pi/4))/(tan(pi/4)*tan(x) + 1),
  {
  have : tan(-x + pi/4) = tan((pi/4) - (x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw tan_sub,
  field_simp,
  ring_exp,
  repeat {assumption},
  },
  rw this,
  rw tan_pi_div_four,
  rw tan_eq_sin_div_cos,
  have : 1*(sin(x)/cos(x)) + 1  =  (sin(x) + cos(x))/cos(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : -(sin(x)/cos(x)) + 1  =  (-sin(x) + cos(x))/cos(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : (sin(x) + cos(x))**2*((-sin(x) + cos(x))/cos(x)/((sin(x) + cos(x))/cos(x))) = (sin(x) + cos(x))*(-sin(x) + cos(x)),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have :(sin(x) + cos(x))*(-sin(x) + cos(x)) =  -sin(x)**2 + cos(x)**2,
  {
  ring_exp,
  },
  rw this,
  have : -sin(x)**2 + cos(x)**2  =  cos(2*x),
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
  have : 2*cos(x)**2 - 1  =  cos(2*x),
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
  field_simp,
end

