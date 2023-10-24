import trigo_import
open real
open_locale real
variables (x y : ℝ)

lemma Trigo_1_150_YLPG : sqrt(3)*sin(2*pi/3) + 2*cos(pi/3)**2=2:=
begin
  rw cos_pi_div_three,
  have : sin(2*pi/3)  =  sin(pi/3),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
  norm_num,
  ring_exp,
  rw sq_sqrt,
  norm_num,
  repeat {linarith},
end

lemma Trigo_1_151_EOYC (h0 : cos(pi/3) ≠ 0) (h1 : 1 + tan(pi/3) * tan(pi/18) ≠ 0) (h2 : cos(pi/18) ≠ 0) (h3: sin(2*pi/9) ≠ 0) : (-tan(pi/18) + sqrt(3))*sin(2*pi/9)=1:=
begin
  rw ← tan_pi_div_three,
  have : -tan(pi/18) + tan(pi/3)  =  (tan(pi/18)*tan(pi/3) + 1)*tan(5*pi/18),
  {
  rw neg_add_eq_sub,
  rw tan_sub_tan,
  have : tan((pi/3) - (pi/18)) = tan (5*pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  repeat {rw tan_eq_sin_div_cos},
  have : cos(5*pi/18)  =  sin(2*pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  have : sin (π / 18) / cos (π / 18) * (sin (π / 3) / (1 / 2)) = 2*sin(pi/18)*sin(pi/3)/cos(pi/18),
  {
    field_simp,
    ring_exp,
  },
  rw this,
  have : 2*sin(pi/18)*sin(pi/3)/cos(pi/18) + 1  =  (2*sin(pi/18)*sin(pi/3) + cos(pi/18))/cos(pi/18),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_three, -cos_pi_div_three],
  },
  rw this,
  have : cos(pi/18)  =  2*cos(pi/18)*cos(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : 2*sin(pi/18)*sin(pi/3) + 2*cos(pi/18)*cos(pi/3)  =  2*cos(5*pi/18),
  {
  have : cos(5*pi/18) = sin(pi/18)*sin(pi/3) + cos(pi/18)*cos(pi/3),
  {
  have : cos(5*pi/18) = cos((pi/3) - (pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_sub,
  ring,
  },
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  field_simp,
  left,
  have : 2*cos(5*π/18)*2*sin(5*π/18) = 4*sin(5*π/18)*cos(5*π/18),
  {
    ring,
  },
  rw this,
  have : 4*sin(5*pi/18)*cos(5*pi/18)  =  2*sin(5*pi/9),
  {
  have : sin (5*pi/9) = sin(2*(5*pi/18)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  ring,
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
end

lemma Trigo_1_152_LXYX (h0 : cos(x)**2 ≠ 0) : sin(x)*cos(x)**2 - 2*sin(x) + sin(x)/cos(x)**2-sin(x)**5/cos(x)**2=0:=
begin
  have : sin(x)*cos(x)**2 - 2*sin(x) + sin(x)/cos(x)**2 - sin(x)**5/cos(x)**2 = -sin(x)**5/cos(x)**2 + sin(x)*cos(x)**2 - 2*sin(x) + sin(x)/cos(x)**2,
  {
    ring,
  },
  rw this,
  have : -sin(x)**5/cos(x)**2 + sin(x)*cos(x)**2  =  (-sin(x)**5 + sin(x)*cos(x)**4)/cos(x)**2,
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : -sin(x)**5 + sin(x)*cos(x)**4  =  (-sin(x)**4 + cos(x)**4)*sin(x),
  {
  ring_exp,
  },
  rw this,
  have : -sin(x)**4 + cos(x)**4  =  (-sin(x)**2 + cos(x)**2)*(sin(x)**2 + cos(x)**2),
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  simp,
  have : (-sin(x)**2 + cos(x)**2)*sin(x)/cos(x)**2 - 2*sin(x) + sin(x)/cos(x)**2  =  ((-sin(x)**2 + cos(x)**2)*sin(x) - 2*sin(x)*cos(x)**2 + sin(x))/cos(x)**2,
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : (-sin(x)**2 + cos(x)**2)*sin(x)  =  -sin(x)**3 + sin(x)*cos(x)**2,
  {
  ring_exp,
  },
  rw this,
  have : -sin(x)**3 = sin(x)*cos(x)**2  -sin(x)*(sin(x)**2 + cos(x)**2),
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  norm_num,
  left,
  ring_exp,
end

lemma Trigo_1_153_IKXK (h0 : cos(67*pi/180) ≠ 0) (h1 : cos(17*pi/45) ≠ 0) (h2 : 1 - tan(17*pi/45) * tan(67*pi/180) ≠ 0) : -tan(67*pi/180)*tan(17*pi/45) + tan(67*pi/180) + tan(17*pi/45)=-1:=
begin
  rw add_assoc,
  have : tan(67*pi/180) + tan(17*pi/45)  =  (-tan(67*pi/180)*tan(17*pi/45) + 1)*tan(3*pi/4),
  {
  rw add_comm,
  rw tan_add_tan,
  have : tan((17*pi/45) + (67*pi/180)) = tan (3*pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  rw tan_three_pi_div_four,
  norm_num,
end

lemma Trigo_1_154_XUWJ (h0 : cos(pi/6) ≠ 0) (h1 : 1 - tan(pi/6) * tan(pi/12) ≠ 0) (h2 : cos(pi/12) ≠ 0) : tan(pi/12)*tan(pi/6) + tan(pi/12) + tan(pi/6)=1:=
begin
  rw add_assoc,
  have : tan(pi/12) + tan(pi/6)  =  (-tan(pi/12)*tan(pi/6) + 1)*tan(pi/4),
  {
  rw add_comm,
  rw tan_add_tan,
  have : tan((pi/6) + (pi/12)) = tan (pi/4),
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

lemma Trigo_1_155_TOUL (h0 : cos(29*pi/180) ≠ 0) : (-sin(29*pi/180)*cos(pi/6) + sin(59*pi/180))/cos(29*pi/180)=1/2:=
begin
  have : sin(59*pi/180)  =  sin(29*pi/180)*cos(pi/6) + sin(pi/6)*cos(29*pi/180),
  {
  have : sin(59*pi/180) = sin((pi/6) + (29*pi/180)),
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
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_1_156_EDMO (h0 : cos(2*pi/9) ≠ 0) (h1 : 1 - tan(pi/9) * tan(2*pi/9) ≠ 0) (h2 : cos(pi/9) ≠ 0) (h3 : tan(pi/9) ≠ 0) (h4 : tan(2*pi/9) ≠ 0) : (tan(pi/9) + tan(2*pi/9) + tan(2*pi/3))/(tan(pi/9)*tan(2*pi/9))=-sqrt(3):=
begin
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
  rw tan_two_pi_div_three,
  have : (-tan(pi/9)*tan(2*pi/9) + 1)*sqrt(3)  =  -sqrt(3)*tan(pi/9)*tan(2*pi/9) + sqrt(3),
  {
  ring_exp,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_1_157_ZCQS (h0 : cos(2*pi/9) ≠ 0) (h1 : 1 - tan(pi/9) * tan(2*pi/9) ≠ 0) (h2 : cos(pi/9) ≠ 0) : sqrt(3)*tan(pi/9)*tan(2*pi/9) + tan(pi/9) + tan(2*pi/9)=sqrt(3):=
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

lemma Trigo_1_158_WJWZ (h0 : sin(8*pi/9) ≠ 0) (h1 : sin(pi/9) ≠ 0) : cos(pi/9)*cos(2*pi/9)*cos(pi/3)*cos(4*pi/9)=1/16:=
begin
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
  rw div_mul_eq_mul_div,
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
  have : sin(4*π/9)/2/(2*sin(π/9))*cos(π/3)*cos(4*π/9) = sin(4*π/ 9)*cos(4*π/9)/2/(2*sin(π/9))*cos(π/3),
  {
    ring,
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
  have : sin(pi/9)  =  sin(8*pi/9),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  field_simp,
  ring_exp,
end

lemma Trigo_1_159_TUMT (h0: cos(17*pi/180) ≠ 0) : (-sin(17*pi/180)*cos(pi/6) + sin(47*pi/180))/cos(17*pi/180)=1/2:=
begin
  have : sin(47*pi/180)  =  sin(17*pi/180)*cos(pi/6) + sin(pi/6)*cos(17*pi/180),
  {
  have : sin(47*pi/180) = sin((pi/6) + (17*pi/180)),
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
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_1_160_BMST : sin(17*pi/180)*cos(227*pi/180) + sin(47*pi/180)*sin(73*pi/180)=1/2:=
begin
  have : cos(227*pi/180)  =  -cos(47*pi/180),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (227*pi/180) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(17*pi/180)  =  cos(73*pi/180),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (17*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_neg,
  rw mul_comm,
  rw ← neg_mul,
  have : -cos(47*pi/180)*cos(73*pi/180) + sin(47*pi/180)*sin(73*pi/180)  =  -cos(2*pi/3),
  {
  have : cos(2*pi/3) = -sin(47*pi/180)*sin(73*pi/180) + cos(47*pi/180)*cos(73*pi/180),
  {
  have : cos(2*pi/3) = cos((47*pi/180) + (73*pi/180)),
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
  rw cos_two_pi_div_three,
  norm_num,
end

lemma Trigo_1_161_JYRW (h0 : sin(4) ≤ 0) : sqrt(1 - cos(4)**2)=-sin(4):=
begin
  rw cos_sq',
  norm_num,
  rw sqrt_sq_eq_abs,
  rw abs_eq_neg_self.mpr h0,
end

lemma Trigo_1_162_RSPH : 2*sin(7*pi/36)*cos(5*pi/36) + 2*sin(11*pi/36)*cos(13*pi/36)=sqrt(3):=
begin
  have : sin(7*pi/36)  =  cos(11*pi/36),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/36) (0),
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
  have : sin(11*pi/36)  =  cos(7*pi/36),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (11*pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(13*pi/36)  =  sin(5*pi/36),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (13*pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw add_comm,
  rw mul_right_comm,
  have : 2*sin(5*pi/36)*cos(7*pi/36) + 2*sin(7*pi/36)*cos(5*pi/36)  =  2*sin(pi/3),
  {
  have : sin(pi/3) = sin(5*pi/36)*cos(7*pi/36) + sin(7*pi/36)*cos(5*pi/36),
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
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
  field_simp,
  ring_exp,
end

lemma Trigo_1_163_YAML (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(-x)*cos(-x + pi/2)*cos(x + pi)/(sin(x + 2*pi)*cos(pi - x)*tan(x + pi))=-cos(x):=
begin
  have : sin(-x)  =  -sin(x),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-x + pi/2)  =  sin(x),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-x + pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(x + pi)  =  -cos(x),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(x + 2*pi)  =  sin(x),
  {
  rw sin_eq_sin_add_int_mul_two_pi (x + 2*pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(pi - x)  =  -cos(x),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : tan(x + pi)  =  tan(x),
  {
  rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_1_164_HNWO (h0 : sin(pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : sin(pi/9) ≠ 0) : -sqrt(3)/sin(4*pi/9) + 1/sin(pi/18)=4:=
begin
  have : sin(4*pi/9)  =  cos(pi/18),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : -sqrt(3)/cos(pi/18) + 1/sin(pi/18)  =  (-sqrt(3)*sin(pi/18) + cos(pi/18))/(sin(pi/18)*cos(pi/18)),
  {
  ring_exp,
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  left,
  ring_exp,
  },
  rw this,
  rw neg_mul,
  have : sqrt(3)*sin(pi/18)  =  2*sin(pi/18)*sin(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/18)  =  2*cos(pi/18)*cos(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : sin(π/18)*(2*cos(π/18)*cos(π/3))  =  sin(pi/18)*cos(pi/18),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  rw ← neg_mul,
  rw ← neg_mul,
  have : -2*sin(pi/18)*sin(pi/3) + 2*cos(pi/18)*cos(pi/3)  =  2*cos(7*pi/18),
  {
  have : cos(7*pi/18) = -sin(pi/18)*sin(pi/3) + cos(pi/18)*cos(pi/3),
  {
  have : cos(7*pi/18) = cos((pi/3) + (pi/18)),
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
  have : cos(7*pi/18)  =  sin(pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
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
  field_simp,
  ring,
end

lemma Trigo_1_165_HETW (h0 : cos(73*pi/180) ≠ 0) (h1 : cos(31*pi/90) ≠ 0) (h2 : 1 - tan(31*pi/90) * tan(73*pi/180) ≠ 0) : -tan(31*pi/90)*tan(73*pi/180) + tan(31*pi/90) + tan(73*pi/180)=-1:=
begin
  rw add_assoc,
  have : tan(31*pi/90) + tan(73*pi/180)  =  (-tan(31*pi/90)*tan(73*pi/180) + 1)*tan(3*pi/4),
  {
  rw tan_add_tan,
  have : tan((31*pi/90) + (73*pi/180)) = tan (3*pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(31*pi/90)*tan(73*pi/180) + 1)*tan(3*pi/4)  =  tan(3*pi/4) - tan(31*pi/90)*tan(73*pi/180)*tan(3*pi/4),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_four, -cos_pi_div_four],
  ring_exp,
  },
  rw this,
  have : tan(3*pi/4)  =  -tan(pi/4),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/4) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_four,
  norm_num,
  ring_exp,
end

lemma Trigo_1_166_WAWI (h0 : cos(19*pi/180) ≠ 0) (h1 : cos(13*pi/90) ≠ 0) (h2 : 1 - tan(13*pi/90) * tan(19*pi/180) ≠ 0) : tan(19*pi/180)*tan(13*pi/90) + tan(19*pi/180) + tan(13*pi/90)=1:=
begin
  rw add_assoc,
  have : tan(19*pi/180) + tan(13*pi/90)  =  (-tan(19*pi/180)*tan(13*pi/90) + 1)*tan(pi/4),
  {
  rw add_comm,
  rw tan_add_tan,
  have : tan((13*pi/90) + (19*pi/180)) = tan (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : (-tan(19*pi/180)*tan(13*pi/90) + 1)*tan(pi/4)  =  -tan(19*pi/180)*tan(13*pi/90)*tan(pi/4) + tan(pi/4),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_four, -cos_pi_div_four],
  },
  rw this,
  rw tan_pi_div_four,
  norm_num,
end

lemma Trigo_1_167_EBUX (h0 : cos(x) ≠ 0) (h1 : cos(2*x) ≠ 0) : 2*sin(2*x)*cos(x)**2/((cos(2*x) + 1)*cos(2*x))=tan(2*x):=
begin
  rw tan_eq_sin_div_cos,
  have : cos(2*x) + 1  =  2*cos(x)**2,
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
  field_simp,
  ring_exp,
end

lemma Trigo_1_168_GBIJ : sin(13*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(167*pi/180)=-1/2:=
begin
  have : cos(167*pi/180)  =  -cos(13*pi/180),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (167*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw add_comm,
  rw mul_neg,
  rw ← neg_mul,
  have : -sin(43*pi/180)*cos(13*pi/180) + sin(13*pi/180)*cos(43*pi/180)  =  sin(-pi/6),
  {
  have : sin(-pi/6) = sin((13*pi/180) - (43*pi/180)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  have : sin(-pi/6)  =  -sin(pi/6),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_1_169_PTGK (h0: cos(2) + sin(2) ≥ 0) : sqrt(2*sin(2)*cos(2) + 1)=sin(2)+cos(2):=
begin
  have : 2*sin(2)*cos(2) + 1  = 2*sin(2)*cos(2) + cos(2)**2 + sin(2)**2,
  {
  rw add_assoc,
  rw cos_sq_add_sin_sq,
  },
  rw this,
  have : 2*sin(2)*cos(2) + cos(2)**2 + sin(2)**2  =  (cos(2) + sin(2))**2,
  {
  ring_exp,
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h0,
  ring,
end

lemma Trigo_1_170_YMAF (h0 : 1-tan(pi/9)*tan(pi/18) ≠ 0) (h1 : tan((pi/9)+(pi/18)) ≠ 0) (h2 : cos(pi/18) ≠ 0) (h3 : cos(pi/9) ≠ 0) (h4 : sqrt 3 ≠ 0) : sqrt(3)*(tan(pi/18) + tan(pi/9)) + tan(pi/18)*tan(pi/9)=1:=
begin
  have : tan(pi/18)*tan(pi/9)  =  -(tan(pi/18) + tan(pi/9))/tan(pi/6) + 1,
  {
  rw mul_comm,
  rw tan_mul_tan',
  have : tan((pi/9) + (pi/18)) = tan (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  field_simp,
  left,
  ring,
  repeat {assumption},
  },
  rw this,
  rw tan_pi_div_six,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_1_171_MLEC (h0 : sin(x) ≠ 0) (h1 : tan(x) ≠ 0) : sin(pi - x)*cos(-x + 2*pi)*tan(x)*tan(-x + 3*pi/2)/sin(x + pi)=-cos(x):=
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
  have : tan(-x + 3*pi/2)  =  1/tan(x),
  {
  rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (-x + 3*pi/2) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(x + pi)  =  -sin(x),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw div_neg,
  field_simp,
  ring_exp,
end

lemma Trigo_1_172_FYAM : sin(pi/12)*cos(3*pi/4) + sin(pi/4)*cos(pi/12)=1/2:=
begin
  have : cos(3*pi/4)  =  -cos(pi/4),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/4) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_neg,
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

lemma Trigo_1_173_HJXB : sin(13*pi/180)*sin(73*pi/180) + sin(103*pi/180)*sin(163*pi/180)=1/2:=
begin
  have : sin(103*pi/180)  =  cos(13*pi/180),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (103*pi/180) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(163*pi/180)  =  sin(17*pi/180),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (163*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(73*pi/180)  =  cos(17*pi/180),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (73*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_comm (cos(13*π/180)) (sin(17*π/180)),
  have : sin(13*pi/180)*cos(17*pi/180) + sin(17*pi/180)*cos(13*pi/180)  =  sin(pi/6),
  {
  have : sin(pi/6) = sin((13*pi/180) + (17*pi/180)),
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

lemma Trigo_1_174_XOWB (h0 : cos(pi/8) ≠ 0) (h1 : -sin(π/8)**2 + cos(π/8)**2 ≠ 0) : tan(pi/8)/(1 - tan(pi/8)**2)=1/2:=
begin
  rw tan_eq_sin_div_cos,
  rw div_pow,
  have :1 -sin(pi/8)**2/cos(pi/8)**2   =  (-sin(pi/8)**2 + cos(pi/8)**2)/cos(pi/8)**2,
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_eight, -cos_pi_div_eight],
  ring_exp,
  },
  rw this,
  have : sin(π/8)/cos(π/8)/((-sin(π/8)**2 + cos(π/8)**2)/cos(π/8)**2) = sin(π/8)*cos(π/8)/(-sin(π/8)**2 + cos(π/8)**2),
  {
    field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_eight, -cos_pi_div_eight],
    ring_exp,
  },
  rw this,
  have : sin(pi/8)*cos(pi/8)  =  sin(pi/4)/2,
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
  have : -sin(pi/8)**2 + cos(pi/8)**2  =  cos(pi/4),
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
  rw sin_pi_div_four,
  rw cos_pi_div_four,
  field_simp,
  ring_exp,
end

lemma Trigo_1_175_HAOV : sin(13*pi/180)*sin(47*pi/180) - sin(77*pi/180)*cos(47*pi/180)=-1/2:=
begin
  have : sin(77*pi/180)  =  cos(13*pi/180),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (77*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sub_eq_neg_add,
  rw ← neg_mul,
  have : -cos(13*pi/180)*cos(47*pi/180) + sin(13*pi/180)*sin(47*pi/180)  =  -cos(pi/3),
  {
  have : cos(pi/3) = -sin(13*pi/180)*sin(47*pi/180) + cos(13*pi/180)*cos(47*pi/180),
  {
  have : cos(pi/3) = cos((13*pi/180) + (47*pi/180)),
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

lemma Trigo_1_176_WMJO (h0 : cos (pi/8) ≠ 0) : tan(pi/8)=sqrt(2)-1:=
begin
  have : tan(pi/8)  =  (1 - cos(pi/4))/sin(pi/4),
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
  rw tan_div_two,
  repeat {assumption},
  },
  rw this,
  rw cos_pi_div_four,
  rw sin_pi_div_four,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_1_177_THTG : sin(pi/12)*sin(pi/6)*sin(5*pi/12)=1/8:=
begin
  have : sin(5*pi/12)  =  cos(pi/12),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_right_comm,
  have : sin(pi/12)*cos(pi/12)  =  sin(pi/6)/2,
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

lemma Trigo_1_178_MWGJ (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : cos(x) + 1 ≠ 0) : (-sin(x) + cos(x))*tan(x) + (sin(x) + tan(x))/(1/tan(x) + 1/sin(x))=sin(x):=
begin
  rw tan_eq_sin_div_cos,
  rw ← mul_div_assoc,
  have : (-sin(x) + cos(x))*sin(x)/cos(x)  =  -sin(x)**2/cos(x) + sin(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : sin(x) + sin(x)/cos(x)  =  (sin(x)*cos(x) + sin(x))/cos(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  norm_num,
  have : cos(x)/sin(x) + 1/sin(x)  =  (cos(x) + 1)/sin(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : sin(x)*cos(x) + sin(x)  =  (cos(x) + 1)*sin(x),
  {
  ring_exp,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_1_179_LPWJ (h0: -sin 2 + cos 2 ≤ 0) : sqrt(2*sin(-2 + 2*pi)*cos(-2 + 2*pi) + 1)=sin(2)-cos(2):=
begin
  have : 2*sin(-2 + 2*pi)*cos(-2 + 2*pi)  =  sin(-4 + 4*pi),
  {
  have : sin (-4 + 4*pi) = sin(2*(-2 + 2*pi)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : sin(-4 + 4*pi)  =  2*sin(-2 + 2*pi)*cos(-2 + 2*pi),
  {
  have : sin (-4 + 4*pi) = sin(2*(-2 + 2*pi)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : 2*sin(-2 + 2*π)*cos(-2 + 2*π) + 1 = 2*sin(-2 + 2*π)*cos(-2 + 2*π) + cos(-2 + 2*pi)**2 + sin(-2 + 2*pi)**2,
  {
  rw add_assoc,
  rw cos_sq_add_sin_sq,
  },
  rw this,
  have : 2*sin(-2 + 2*pi)*cos(-2 + 2*pi) + cos(-2 + 2*pi)**2 + sin(-2 + 2*pi)**2  =  (sin(-2 + 2*pi) + cos(-2 + 2*pi))**2,
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : sin(-2 + 2*pi)  =  -sin(2),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-2 + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-2 + 2*pi)  =  cos(2),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-2 + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_neg_self.mpr h0,
  ring,
end

lemma Trigo_1_180_DFLS (h0 : -cos(pi/9) + sin(pi/9) ≠ 0) (h1 : cos(pi/9) ≥ 0) (h2 : -cos(pi/9) + sin(pi/9) ≤ 0) : sqrt(-2*sin(pi/9)*cos(pi/9) + 1)/(-sqrt(1 - sin(pi/9)**2) + sin(8*pi/9))=-1:=
begin
  have : -2*sin(pi/9)*cos(pi/9) + 1 = -2*sin(pi/9)*cos(pi/9) + sin(pi/9)**2 + cos(pi/9)**2,
  {
  rw add_assoc,
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : -2*sin(pi/9)*cos(pi/9) + sin(pi/9)**2 + cos(pi/9)**2 = (-cos(pi/9) + sin(pi/9))**2,
  {
  ring_exp,
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
  rw sqrt_sq_eq_abs,
  rw abs_eq_neg_self.mpr h2,
  have : 1 - sin (π / 9) ** 2 = cos(pi/9)**2,
  {
    rw cos_sq',
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h1,
  field_simp,
end

lemma Trigo_1_181_YEAI (h0 : cos(y) ≠ 0) (h1 : cos(x) ≠ 0) : sin(x - y)/(cos(x)*cos(y))-tan(x)+tan(y)=0:=
begin
  have : sin(x - y) = sin(x)*cos(y) - sin(y)*cos(x),
  {
  have : sin(x-y) = sin((x) - (y)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_sub,
  ring,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  rw tan_eq_sin_div_cos,
  rw sub_eq_add_neg,
  rw add_assoc,
  rw neg_div',
  have : -sin(x)/cos(x) + sin(y)/cos(y) = (-sin(x)*cos(y) + sin(y)*cos(x))/(cos(x)*cos(y)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  field_simp,
end

lemma Trigo_1_182_TJRB (h0 : cos(x) ≠ 0) : (sin(-x + pi/6) + sin(x + pi/6))/cos(x)=1:=
begin
  have : sin(-x + pi/6) = -sin(x - pi/6),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
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
  rw this,
  rw sin_pi_div_six,
  field_simp,
end

lemma Trigo_1_183_DIYN : cos(pi/12)*cos(5*pi/12)=1/4:=
begin
  have : cos(5*pi/12) = sin(pi/12),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_comm,
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

lemma Trigo_1_184_ROGD (h0 : cos(x) ≠ 0) (h1 : sin(x) ≠ 0) : sin(-x + 3*pi/2)*sin(x - 3*pi)*cos(-x + 2*pi)**2/(sin(-x - pi)*sin(x + pi/2)*cos(-x - pi))=-cos(x):=
begin
  have : sin(-x + 3*pi/2) = -cos(x),
  {
  rw sin_eq_neg_cos_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 3*pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(x - 3*pi) = -sin(x),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x - 3*pi) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-x + 2*pi) = cos(-x),
  {
  rw cos_eq_cos_add_int_mul_two_pi (-x + 2*pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-x) = cos(x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x) (0),
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
  have : sin(x + pi/2) = cos(x),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-x - pi) = -cos(x),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_1_185_MACM (h0 : 2 ≠ 0) : sin(x)*sin(x - pi/3) + cos(x)*cos(x - pi/3)=1/2:=
begin
  have : sin(x - pi/3) = sin(x)*cos(pi/3) - sin(pi/3)*cos(x),
  {
  have : sin(x-pi/3) = sin((x) - (pi/3)),
  {
  apply congr_arg,
  ring,
  },
  rw sin_sub,
  ring,
  },
  rw this,
  have : cos(x - pi/3) = sin(pi/3)*sin(x) + cos(pi/3)*cos(x),
  {
  have : cos(x-pi/3) = cos((x) - (pi/3)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_sub,
  ring,
  },
  rw this,
  rw sin_pi_div_three,
  rw cos_pi_div_three,
  have : cos(x)*(sqrt(3)/2*sin(x) + 1/2*cos(x))= sqrt(3)*sin(x)*cos(x)/2 + cos(x)**2/2,
  {
  ring_exp,
  },
  rw this,
  have : sin(x)*(sin(x)*(1/2) - sqrt(3)/2*cos(x)) = sin(x)**2/2 - sqrt(3)*sin(x)*cos(x)/2,
  {
  ring_exp,
  },
  rw this,
  have : sin(x)**2/2 - sqrt(3)*sin(x)*cos(x)/2 + (sqrt(3)*sin(x)*cos(x)/2 + cos(x)**2/2) = sin(x)**2/2 + cos(x)**2/2,
  {
    ring,
  },
  rw this,
  have : sin(x)**2/2 + cos(x)**2/2 = 1/2,
  {
  have : sin(x)**2 + cos(x)**2 = 1,
  {
  rw sin_sq_add_cos_sq,
  },
  linarith,
  },
  rw this,
end

lemma Trigo_1_186_IQRK (h0 : cos(3*pi/5) ≤ 0) : sqrt(1 - sin(3*pi/5)**2)=-cos(3*pi/5):=
begin
  have : 1 - sin(3*pi/5)**2 = cos(3*pi/5)**2,
  {
  rw cos_sq',
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_neg_self.mpr h0,
end

lemma Trigo_1_187_TXAZ : sin(pi/9)*cos(23*pi/36) + sin(7*pi/18)*cos(5*pi/36)=sqrt(2)/2:=
begin
  have : sin(pi/9)*cos(23*pi/36) = -sin(19*pi/36)/2 + sin(3*pi/4)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((23*pi/36) + (pi/9)) = sin (3*pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((23*pi/36) - (pi/9)) = sin (19*pi/36),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(7*pi/18)*cos(5*pi/36) = sin(pi/4)/2 + sin(19*pi/36)/2,
  {
  rw sin_mul_cos,
  have : sin((7*pi/18) + (5*pi/36)) = sin (19*pi/36),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((7*pi/18) - (5*pi/36)) = sin (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  have : -sin(19*π/36)/2 + sin(3*π/4)/2 + (sin(π/4)/2 + sin(19*π/36)/2) = sin(pi/4)/2 + sin(3*pi/4)/2,
  {
    ring,
  },
  rw this,
  have : sin(3*pi/4) = sin(pi/4),
  {
    rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (3*pi/4) (0),
    apply congr_arg,
    simp,
    ring,
  },
  rw this,
  rw sin_pi_div_four,
  norm_num,
end

lemma Trigo_1_188_BDYM : -sin(11*pi/6)*cos(25*pi/12) + sin(25*pi/12)*cos(11*pi/6)=sqrt(2)/2:=
begin
  rw add_comm,
  rw neg_mul,
  rw ← sub_eq_add_neg,
  have : sin(25*pi/12)*cos(11*pi/6) - sin(11*pi/6)*cos(25*pi/12) = sin(pi/4),
  {
  have : sin(pi/4) = sin((25*pi/12) - (11*pi/6)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  rw sin_pi_div_four,
end

lemma Trigo_1_189_KEAM : sin(pi/60)*cos(pi/15) + cos(pi/60)*cos(13*pi/30)=(sqrt(2)*(sqrt(3)-1))/4:=
begin
  have : cos(13*pi/30) = sin(pi/15),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (13*pi/30) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_comm (cos(π/60)) (sin(π/15)),
  have : sin(pi/60)*cos(pi/15) + sin(pi/15)*cos(pi/60) = sin(pi/12),
  {
  have : sin(pi/12) = sin((pi/15) + (pi/60)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
  },
  rw this,
  rw sin_pi_div_twelve,
  field_simp,
  ring_exp,
  rw ← sqrt_mul,
  ring,
  repeat {linarith},
end

lemma Trigo_1_190_SZEJ (h0 : cos(x) ≠ 0) (h1 : sin(x) ≠ 0) : sin(x + pi)**2*cos(x + pi)/(cos(-x - pi)**3*tan(-x - 2*pi)*tan(x + pi))=-1:=
begin
  have : sin(x + pi) = -sin(x),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (x + pi) (-1),
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
  have : cos(-x - pi) = cos(x + pi),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x - pi) (0),
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
  have : tan(-x - 2*pi) = -tan(x),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-x - 2*pi) (-2),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : tan(x + pi) = tan(x),
  {
  rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_1_191_VIFV (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(-x + 2*pi)*cos(x + pi)/(sin(-x - pi)*sin(-x + 3*pi)*cos(pi - x))=-1/sin(x):=
begin
  have : sin(-x + 2*pi) = -sin(x),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
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
  have : sin(-x - pi) = sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
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

lemma Trigo_1_192_NTYS : 2 - (sqrt(3)*sin(pi/4) - cos(pi/4))**2=sqrt(3):=
begin
  rw cos_pi_div_four,
  rw sin_pi_div_four,
  ring_exp,
  repeat {rw sq_sqrt},
  ring,
  repeat {linarith},
end

lemma Trigo_1_193_QDVP : 2*cos(pi/8)**2 - 1=sqrt(2)/2:=
begin
  have : 2*cos(pi/8)**2 - 1 = cos(pi/4),
  {
  have : cos (pi/4) = cos(2*(pi/8)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  },
  rw this,
  rw cos_pi_div_four,
end

lemma Trigo_1_194_PAUS (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : sin(-x + 2*pi)*cos(-x + 11*pi/2)*cos(x + pi)/(sin(-x - pi)*sin(-x + 3*pi)*sin(x + 9*pi/2)*cos(pi - x))=1/cos(x):=
begin
  have : sin(-x + 2*pi) = -sin(x),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x + 2*pi) (1),
  repeat {apply congr_arg _},
  simp,
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
  have : cos(-x + 11*pi/2) = -sin(x),
  {
  rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 11*pi/2) (2),
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
  have : cos(pi - x) = -cos(x),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
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
  have : sin(x + 9*pi/2) = cos(x),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (x + 9*pi/2) (-3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
end

lemma Trigo_1_195_TRHQ (h0 : sin(pi/18) ≥ 0) (h1 : -cos(pi/18) + sin(pi/18) ≤ 0) (h2 : -sin(pi/18) + cos(pi/18) ≠ 0) : sqrt(-2*sin(pi/18)*cos(pi/18) + 1)/(-sqrt(1 - cos(17*pi/18)**2) + cos(pi/18))=1:=
begin
  have : 1 - cos(17*pi/18)**2 = sin(17*pi/18)**2,
  {
    rw sin_sq,
  },
  rw this,
  have : sin(17*pi/18) = sin(pi/18),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (17*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h0,
  have : -2*sin(pi/18)*cos(pi/18) + 1 = -2*sin(pi/18)*cos(pi/18) + sin(pi/18)**2 + cos(pi/18)**2,
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
  rw abs_eq_neg_self.mpr h1,
  field_simp,
end

lemma Trigo_1_196_IFKW : sin(-x + 13*pi/36)*cos(x - pi/9) + cos(-x + 13*pi/36)*cos(-x + 11*pi/18)=sqrt(2)/2:=
begin
  have : cos(-x + 11*pi/18) = sin(x - pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-x + 11*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_comm (cos(-x + 13*π/36)) (sin(x - π/9)),
  have : sin(-x + 13*pi/36)*cos(x - pi/9) + sin(x - pi/9)*cos(-x + 13*pi/36) = sin(pi/4),
  {
  have : sin(pi/4) = sin((x - pi/9) + (-x + 13*pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add (x - pi/9) (-x + 13*pi/36),
  ring,
  },
  rw this,
  rw sin_pi_div_four,
end

lemma Trigo_1_197_ZSYQ (h0 : sin(5*pi/18) ≠ 0) : (sin(pi/18) - sqrt(3)*cos(pi/18))/cos(2*pi/9)=-2:=
begin
  have : sqrt(3)*cos(pi/18) = 2*sin(pi/3)*cos(pi/18),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : sin(pi/18) = 2*sin(pi/18)*cos(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  rw sub_eq_neg_add,
  rw ← neg_mul,
  rw ← neg_mul,
  have : -2*sin(pi/3)*cos(pi/18) + 2*sin(pi/18)*cos(pi/3) = 2*sin(-5*pi/18),
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
  have : cos(2*pi/9) = sin(5*pi/18),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-5*pi/18) = -sin(5*pi/18),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
end

lemma Trigo_1_198_UYVG : -sin(2*pi/9)*cos(8*pi/9) + sin(10*pi/9)*cos(7*pi/9)=sqrt(3)/2:=
begin
  rw neg_mul,
  have : sin(2*pi/9)*cos(8*pi/9) = -sin(2*pi/3)/2 + sin(10*pi/9)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((8*pi/9) + (2*pi/9)) = sin (10*pi/9),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((8*pi/9) - (2*pi/9)) = sin (2*pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(10*pi/9)*cos(7*pi/9) = sin(17*pi/9)/2 + sin(pi/3)/2,
  {
  rw sin_mul_cos,
  have : sin((10*pi/9) + (7*pi/9)) = sin (17*pi/9),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((10*pi/9) - (7*pi/9)) = sin (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(17*pi/9) = -sin(8*pi/9),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (17*pi/9) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(pi/3) = sin(2*pi/3),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi/3) (0),
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
  have : sin(10*pi/9) = -sin(pi/9),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (10*pi/9) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_two_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_1_199_EXFT (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) (h2 : cos(2*x) ≠ 0) : 2*(1 - cos(2*x))*cos(x)**2/(sin(2*x)*cos(2*x))=tan(2*x):=
begin
  have : 1 - cos(2*x) = 2*sin(x)**2,
  {
  have : sin(x)**2 = 1/2 - cos(2*x)/2,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_two_mul'',
  ring,
  },
  linarith,
  },
  rw this,
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
  field_simp,
  ring_exp,
end