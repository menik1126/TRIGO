import trigo_import
open real
open_locale real
variables (x y : ℝ)




lemma Trigo_6_400_MTEG (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : (1 + 1/tan(x))*cos(x) + (tan(x) + 1)*sin(x)-1/cos(x)-1/sin(x)=0:=
begin
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  have : (1 + cos(x)/sin(x))*cos(x) + (sin(x)/cos(x) + 1)*sin(x) - 1/cos(x) - 1/sin(x)  =  (sin(x)**3 + sin(x)**2*cos(x) + sin(x)*cos(x)**2 + cos(x)**3 - sin(x) - cos(x))/(sin(x)*cos(x)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : sin(x)**3 + sin(x)**2*cos(x) + sin(x)*cos(x)**2 + cos(x)**3  =  (sin(x) + cos(x))*(sin(x)**2 + cos(x)**2),
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  norm_num,
end

lemma Trigo_6_401_GXBA : sin(13*pi/180)**2 - sin(13*pi/180)*cos(17*pi/180) + cos(17*pi/180)**2=3/4:=
begin
  have : cos(17*pi/180)  =  sin(73*pi/180),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (17*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(13*pi/180)**2 - sin(13*pi/180)*sin(73*pi/180) + sin(73*pi/180)**2  =  sin(13*pi/180)*sin(73*pi/180) + (-sin(73*pi/180) + sin(13*pi/180))**2,
  {
  ring_exp,
  },
  rw this,
  have : -sin(73*pi/180) + sin(13*pi/180)  =  2*sin(-pi/6)*cos(43*pi/180),
  {
  rw neg_add_eq_sub,
  rw sin_sub_sin,
  have : cos(((13*pi/180) + (73*pi/180))/2) = cos (43*pi/180),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((13*pi/180) - (73*pi/180))/2) = sin(-pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
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
  have : sin(13*pi/180)*sin(73*pi/180)  =  -cos(43*pi/90)/2 + cos(-pi/3)/2,
  {
  rw sin_mul_sin,
  have : cos((13*pi/180) + (73*pi/180)) = cos (43*pi/90),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((13*pi/180) - (73*pi/180)) = cos (-pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : cos(-pi/3)  =  cos(pi/3),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  have : cos(43*pi/90)  =  -sin(43*pi/180)**2 + cos(43*pi/180)**2,
  {
  have : cos (43*pi/90) = cos(2*(43*pi/180)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  ring_nf,
  rw ← add_assoc,
  have : 1/2*sin(43*pi/180)**2 + 1/2*cos(43*pi/180)**2  =  1/2,
  {
  have : sin(43*pi/180)**2 + cos(43*pi/180)**2 = 1,
  {
  rw sin_sq_add_cos_sq,
  },
  linarith,
  },
  rw this,
  norm_num,
end

lemma Trigo_6_402_DMDU (h0 : 1 - tan(pi/18) * tan(5*pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : cos(5*pi/18) ≠ 0) : sqrt(3)*tan(pi/18)*tan(5*pi/18) + tan(pi/18) + tan(5*pi/18)=sqrt(3):=
begin
  rw add_assoc,
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
  ring_exp,
end

lemma Trigo_6_403_YJZW : sin(pi/9)**2 + sqrt(3)*sin(pi/9)*cos(4*pi/9) + cos(4*pi/9)**2=1/4:=
begin
  rw sin_sq,
  have : 1-cos(π/9)**2 + sqrt(3)*sin(π/9)*cos(4*π/9) + cos(4*π/9)**2 = -cos(π/9)**2 + cos(4*π/9)**2 + 1 + sqrt(3)*sin(π/9)*cos(4*π/9),
  {
    ring,
  },
  rw this,
  have : -cos(pi/9)**2 + cos(4*pi/9)**2  =  (-cos(pi/9) + cos(4*pi/9))*(cos(4*pi/9) + cos(pi/9)),
  {
  ring_exp,
  },
  rw this,
  have : -cos(pi/9) + cos(4*pi/9)  =  -2*sin(pi/6)*sin(5*pi/18),
  {
  rw neg_add_eq_sub,
  rw cos_sub_cos,
  have : sin(((4*pi/9) + (pi/9))/2) = sin (5*pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((4*pi/9) - (pi/9))/2) = sin(pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : cos(4*pi/9) + cos(pi/9)  =  2*cos(pi/6)*cos(5*pi/18),
  {
  rw cos_add_cos,
  have : cos(((4*pi/9) + (pi/9))/2) = cos (5*pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos(((4*pi/9) - (pi/9))/2) = cos(pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw sin_pi_div_six,
  have : (-2)*(1/2)*sin(5*π/18)*(2*cos(π/6)*cos(5*π/18)) = (-2)*(1/2)*(sin(5*π/18)*cos(5*π/18))*(2*cos(π/6)),
  {
    ring,
  },
  rw this,
  have : sin(5*pi/18)*cos(5*pi/18)  =  sin(5*pi/9)/2,
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
  have : sin(5*pi/9)  =  cos(pi/18),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (5*pi/9) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_assoc (sqrt(3)) (sin(π/9)) (cos(4*π/9)),
  have : sin(pi/9)*cos(4*pi/9)  =  -sin(pi/3)/2 + sin(5*pi/9)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((4*pi/9) + (pi/9)) = sin (5*pi/9),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((4*pi/9) - (pi/9)) = sin (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
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
  rw cos_pi_div_six,
  rw sin_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_6_404_BEVX (h0 : sin(x) ≠ 0) : cos(x)*cos(2*x)*cos(4*x)=sin(8*x)/(8*sin(x)):=
begin
  have : sin(8*x)  =  2*sin(4*x)*cos(4*x),
  {
  have : sin (8*x) = sin(2*(4*x)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
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
  field_simp,
  ring_exp,
end

lemma Trigo_6_405_KQQA (h0 : sin(pi/36) ≠ 0) (h1 : sin(pi/12) ≠ 0) (h2 : 2 - sqrt(3) ≠ 0) : (sin(pi/12)*cos(pi/36) - sin(pi/9))/(cos(pi/36)*cos(pi/12) - cos(pi/9))=-2-sqrt(3):=
begin
  have : sin(pi/9) = sin(pi/36)*cos(pi/12) + sin(pi/12)*cos(pi/36),
  {
  have : sin(pi/9) = sin((pi/12) + (pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
  },
  rw this,
  have : cos(pi/9) = -sin(pi/36)*sin(pi/12) + cos(pi/36)*cos(pi/12),
  {
  have : cos(pi/9) = cos((pi/12) + (pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_add,
  ring,
  },
  rw this,
  ring_exp,
  have : sin(π/36)*(cos(π/12)*-(sin(π/12)*sin(π/36))⁻¹) = -cos(pi/12)/sin(pi/12),
  {
  field_simp,
  ring,
  },
  rw this,
  rw neg_div,
  rw ← one_div_div,
  rw ← tan_eq_sin_div_cos,
  rw tan_pi_div_twelve,
  field_simp,
  ring_exp,
  rw sq_sqrt,
  ring,
  repeat {linarith},
end

lemma Trigo_6_406_OYPE (h0 : sin(x) ≠ 0) (h1 : cos(x) ≠ 0) : (-sin(x)**4 - cos(x)**4 + 1)/(-sin(x)**6 - cos(x)**6 + 1)=2/3:=
begin
  have : -sin(x)**4 - cos(x)**4  =  -(sin(x)**2 + cos(x)**2)**2 + 2*sin(x)**2*cos(x)**2,
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  have : -sin(x)**6 - cos(x)**6  =  -(sin(x)**2 + cos(x)**2)**3 + 3*sin(x)**4*cos(x)**2 + 3*sin(x)**2*cos(x)**4,
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  norm_num,
  have : -1 + 3*sin(x)**4*cos(x)**2 + 3*sin(x)**2*cos(x)**4 = -1 + (3*sin(x)**4*cos(x)**2 + 3*sin(x)**2*cos(x)**4),
  {
    ring,
  },
  rw this,
  have : 3*sin(x)**4*cos(x)**2 + 3*sin(x)**2*cos(x)**4  =  3*sin(x)**2*cos(x)**2*(sin(x)**2 + cos(x)**2),
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_6_407_RYZJ (h0 : sin(x) ≠ 0) (h1 : sin(x) - cos(x) + 1 ≠ 0) (h2 : sin(x)**2 - sin(x)*cos(x) + sin(x) ≠ 0) (h3 : cos(x) ≠ 0) : ((sin(x) + 1)*tan(x) + sin(x))/((sin(x) + 1)*tan(x) - sin(x))=(tan(x)+sin(x))/(tan(x)*sin(x)):=
begin
  rw tan_eq_sin_div_cos,
  have : sin(x)/cos(x) + sin(x) =  -1/cos(x)*(-sin(x)*cos(x) - sin(x)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : -sin(x)*cos(x) - sin(x)  =  (-cos(x) - 1)*sin(x),
  {
  ring_exp,
  },
  rw this,
  have : (sin(x) + 1) * (sin(x) / cos(x))  =  (sin(x)**2 + sin(x))/cos(x),
  {
  ring_exp,
  },
  rw this,
  have : (sin(x)**2 + sin(x))/cos(x) + sin(x)  =  (sin(x)**2 + sin(x)*cos(x) + sin(x))/cos(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : (sin(x)**2 + sin(x))/cos(x) - sin(x)  =  (sin(x)**2 - sin(x)*cos(x) + sin(x))/cos(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : sin(x)**2 + sin(x)*cos(x) + sin(x)  =  (sin(x) + cos(x) + 1)*sin(x),
  {
  ring_exp,
  },
  rw this,
  have : sin(x)**2 - sin(x)*cos(x) + sin(x)  =  (sin(x) - cos(x) + 1)*sin(x),
  {
  ring_exp,
  },
  rw this,
  field_simp,
  ring_exp,
  have : cos(x) * sin(x) ** 2 = cos(x)*sin(x)**2*(sin(x)**2 + cos(x)**2),
  {
  rw sin_sq_add_cos_sq,
  ring,
  },
  rw this,
  ring,
end

lemma Trigo_6_408_NQVH (h0 : sin(pi/9) ≠ 0) : sqrt(3)*sin(pi/18)*tan(7*pi/18) - 2*cos(2*pi/9) + cos(pi/18)*cos(pi/9)/sin(pi/9)=2:=
begin
  have : tan(7*pi/18)  =  1/tan(pi/9),
  {
  rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  rw sub_add_eq_add_sub,
  have : sqrt(3)*sin(pi/18)*(cos(pi/9)/sin(pi/9)) + cos(pi/18)*cos(pi/9)/sin(pi/9)  =  (sqrt(3)*sin(pi/18) + cos(pi/18))*cos(pi/9)/sin(pi/9),
  {
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
  have : sin(2*pi/9)  =  2*sin(pi/9)*cos(pi/9),
  {
  have : sin (2*pi/9) = sin(2*(pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  ring_exp,
  have : cos(pi/9)**2 = cos(2*pi/9)/2 + 1/2,
  {
  have : cos (2*pi/9) = cos(2*(pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_6_409_DDFZ (h0 : cos(pi/9) ≠ 0) (h1 : sin(pi/9) ≠ 0) : (sqrt(3)*tan(pi/9) - 1)*cos(pi/18)*tan(7*pi/18)=-1:=
begin
  have : tan(7*pi/18)  =  1/tan(pi/9),
  {
  rw tan_eq_one_div_tan_neg_add_pi_div_two_add_int_mul_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  have : sqrt(3)*(sin(pi/9)/cos(pi/9)) - 1 =  (-cos(pi/9) + sqrt(3)*sin(pi/9))/cos(pi/9),
  {
  ring_exp,
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : sqrt(3)*sin(pi/9)  =  2*sin(pi/9)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/9)  =  2*sin(pi/6)*cos(pi/9),
  {
  field_simp,
  },
  rw this,
  rw ← neg_mul,
  rw ← neg_mul,
  have : -2*sin(pi/6)*cos(pi/9) + 2*sin(pi/9)*cos(pi/6)  =  2*sin(-pi/18),
  {
  have : sin(-pi/18) = sin(pi/9)*cos(pi/6) - sin(pi/6)*cos(pi/9),
  {
  have : sin(-pi/18) = sin((pi/9) - (pi/6)),
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
  have : sin(-pi/18)  =  -sin(pi/18),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw div_mul_eq_mul_div,
  rw mul_neg,
  rw ← neg_mul,
  have : -2*sin(pi/18)*cos(pi/18)  =  -sin(pi/9),
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
  ring_exp,
end

lemma Trigo_6_410_RSSE (h0 : cos(pi/15) ≠ 0) (h1 : sin(4*pi/15) ≠ 0) : (sqrt(3)*tan(pi/15) - 3)/((4*cos(pi/15)**2 - 2)*sin(pi/15))=-4*sqrt(3):=
begin
  rw tan_eq_sin_div_cos,
  rw sub_eq_add_neg (4*cos(π/15)**2) 2,
  have : -2  =  -2*cos(pi/15)**2 - 2*sin(pi/15)**2,
  {
  have : sin(pi/15)**2 + cos(pi/15)**2 = 1,
  {
  rw sin_sq_add_cos_sq,
  },
  linarith,
  },
  rw this,
  have : 4*cos(π/15)**2 + ((-2)*cos(π/15)**2 - 2*sin(π/15)**2) = -2*sin(pi/15)**2 + 2*cos(pi/15)**2 ,
  {
  ring,
  },
  rw this,
  have : -2*sin(pi/15)**2 + 2*cos(pi/15)**2  =  2*cos(2*pi/15),
  {
  have : cos(2*pi/15) = -sin(pi/15)**2 + cos(pi/15)**2,
  {
  have : cos (2*pi/15) = cos(2*(pi/15)),
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
  have : sqrt(3)*(sin(pi/15)/cos(pi/15)) - 3  =  (-3*cos(pi/15) + sqrt(3)*sin(pi/15))/cos(pi/15),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : ((-3)*cos(π/15) + sqrt(3)*sin(π/15))/cos(π/15)/(2*cos(2*π/15)*sin(π/15)) = ((-3)*cos(π/15) + sqrt(3)*sin(π/15))/(2*sin(π/15)*cos(pi/15)*cos(2*π/15)),
  {
    field_simp,
    ring_exp,
  },
  rw this,
  have : 2*sin(pi/15)*cos(pi/15) = sin(2*pi/15),
  {
  have : sin (2*pi/15) = sin(2*(pi/15)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : sin(2*pi/15)*cos(2*pi/15) = sin(4*pi/15)/2,
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
  have : cos(pi/15)  =  2*sin(pi/6)*cos(pi/15),
  {
  field_simp,
  },
  rw this,
  have : sqrt(3)*sin(pi/15)  =  2*cos(pi/6)*sin(pi/15),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : (-3)*(2*sin(π/6)*cos(π/15)) + 2*cos(π/6)*sin(π/15) = -2*sin(π/6)*cos(π/15) + 2*cos(π/6)*sin(π/15) - 4*sin(π/6)*cos(π/15),
  {
  ring,
  },
  rw this,
  rw mul_right_comm 2 (cos(π/6)) (sin(π/15)),
  have : -2*sin(pi/6)*cos(pi/15) + 2*sin(pi/15)*cos(pi/6)  =  -2*sin(pi/10),
  {
  have : sin(pi/10) = -sin(pi/15)*cos(pi/6) + sin(pi/6)*cos(pi/15),
  {
  have : sin(pi/10) = sin((pi/6) - (pi/15)),
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
  have : sin(pi/10)  =  cos(2*pi/5),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/10) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  have : (-2)*cos(2*π/5) - 4*(1/2)*cos(π/15) = -2*cos(pi/15) - 2*cos(2*pi/5),
  {
    ring,
  },
  rw this,
  have : -2*cos(pi/15) - 2*cos(2*pi/5)  =  -4*cos(-pi/6)*cos(7*pi/30),
  {
  have : cos(pi/15) + cos(2*pi/5) = 2*cos(-pi/6)*cos(7*pi/30),
  {
  rw cos_add_cos,
  have : cos(((pi/15) + (2*pi/5))/2) = cos (7*pi/30),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos(((pi/15) - (2*pi/5))/2) = cos(-pi/6),
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
  have : cos(-pi/6)  =  cos(pi/6),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  have : cos(7*pi/30)  =  sin(4*pi/15),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/30) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_6_411_BEZS (h0 : cos(2*pi/15) ≠ 0) (h1 : tan((11*pi/90)+(23*pi/180)) ≠ 0) (h2 : 1 - tan(2*pi/15) * tan(7*pi/60) ≠ 0) (h3 : cos(7*pi/60) ≠ 0) (h4 : cos(23*pi/180) ≠ 0) (h5 : 1-tan(11*pi/90)*tan(23*pi/180) ≠ 0) (h6 : cos(11*pi/90) ≠ 0) : (tan(7*pi/60) + 1)*(tan(11*pi/90) + 1)*(tan(23*pi/180) + 1)*(tan(2*pi/15) + 1)=4:=
begin
  have : (tan(7*pi/60) + 1)*(tan(11*pi/90) + 1)*(tan(23*pi/180) + 1)*(tan(2*pi/15) + 1) = (tan(7*pi/60) + 1)*(tan(2*pi/15) + 1)*(tan(11*pi/90) + 1)*(tan(23*pi/180) + 1),
  {
  ring,
  },
  rw this,
  have : (tan(7*pi/60) + 1)*(tan(2*pi/15) + 1)  =  tan(7*pi/60)*tan(2*pi/15) + tan(7*pi/60) + tan(2*pi/15) + 1,
  {
  ring_exp,
  },
  rw this,
  rw add_assoc (tan(7*π/60)*tan(2*π/15)) (tan(7*π/60)) (tan(2*π/15)),
  have : tan(7*pi/60) + tan(2*pi/15)  =  (-tan(7*pi/60)*tan(2*pi/15) + 1)*tan(pi/4),
  {
  rw add_comm,
  rw tan_add_tan,
  have : tan((2*pi/15) + (7*pi/60)) = tan (pi/4),
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
  rw mul_assoc,
  have : (tan(11*pi/90) + 1)*(tan(23*pi/180) + 1)  =  tan(11*pi/90)*tan(23*pi/180) + tan(11*pi/90) + tan(23*pi/180) + 1,
  {
  ring_exp,
  },
  rw this,
  have : tan(11*pi/90)*tan(23*pi/180)  =  -(tan(11*pi/90) + tan(23*pi/180))/tan(pi/4) + 1,
  {
  rw tan_mul_tan',
  have : tan((11*pi/90) + (23*pi/180)) = tan (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  repeat {assumption},
  },
  rw this,
  rw tan_pi_div_four,
  norm_num,
  ring_exp,
end

lemma Trigo_6_412_HKDG (h0 : -sin(pi/36) + cos(pi/36) ≥ 0) (h1 : sin(4*pi/9) ≠ 0) : cos(pi/18)/(sqrt(1 - sin(pi/18))*cos(2*pi/9))=sqrt(2):=
begin
  have : sin(pi/18)  =  2*sin(pi/36)*cos(pi/36),
  {
  have : sin (pi/18) = sin(2*(pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : 1 - 2*sin(π/36)*cos(π/36) = sin(pi/36)**2 + cos(pi/36)**2 - 2*sin(π/36)*cos(π/36),
  {
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : sin(pi/36)**2 + cos(pi/36)**2 -2*sin(pi/36)*cos(pi/36)  =  (-sin(pi/36) + cos(pi/36))**2,
  {
  ring_exp,
  },
  rw this,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h0,
  have : sin(pi/36)  =  cos(17*pi/36),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : -cos(17*pi/36) + cos(pi/36)  =  2*sin(2*pi/9)*sin(pi/4),
  {
  have : -cos(pi/36) + cos(17*pi/36) = -2*sin(2*pi/9)*sin(pi/4),
  {
  rw neg_add_eq_sub,
  rw cos_sub_cos,
  have : sin(((17*pi/36) + (pi/36))/2) = sin (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((17*pi/36) - (pi/36))/2) = sin(2*pi/9),
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
  rw mul_right_comm (2*sin(2*π/9)) (sin(π/4)) (cos(2*π/9)),
  have : 2*sin(2*pi/9)*cos(2*pi/9) = sin(4*pi/9),
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
  have : cos(pi/18)  =  sin(4*pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_four,
  field_simp,
  ring_nf,
  rw sq_sqrt,
  repeat {linarith},
end

lemma Trigo_6_413_QUEC (h0 : cos(pi/36) ≠ 0) : (-sqrt(3)*sin(pi/36) + 2*cos(11*pi/36))/cos(pi/36)=1:=
begin
  have : sqrt(3)  =  2*sin(pi/3),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  rw ← neg_mul,
  rw mul_assoc,
  have : sin(pi/3)*sin(pi/36)  =  -cos(13*pi/36)/2 + cos(11*pi/36)/2,
  {
  rw sin_mul_sin,
  have : cos((pi/3) + (pi/36)) = cos (13*pi/36),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((pi/3) - (pi/36)) = cos (11*pi/36),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : (-2)*(-cos(13*π/36)/2 + cos(11*π/36)/2) + 2*cos(11*π/36) = cos(13*pi/36) + cos(11*pi/36),
  {
  ring,
  },
  rw this,
  have : cos(13*pi/36) + cos(11*pi/36)  =  2*cos(-pi/36)*cos(pi/3),
  {
  rw add_comm,
  rw cos_add_cos,
  have : cos(((11*pi/36) + (13*pi/36))/2) = cos (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos(((11*pi/36) - (13*pi/36))/2) = cos(-pi/36),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : cos(-pi/36)  =  cos(pi/36),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  field_simp,
end

lemma Trigo_6_414_SIUE (h0 : cos(pi/3) ≠ 0) (h1 : cos(pi/15) ≠ 0) (h2 : sin(pi/15) ≠ 0) (h3 : cos(2*pi/15) ≠ 0) (h4 : sin(4*pi/15) ≠ 0) : (tan(pi/15) - sqrt(3))/((2*cos(pi/15)**2 - 1)*sin(pi/15))=-8:=
begin
  have : 2*cos(pi/15)**2 -1  =  cos(2*pi/15),
  {
  have : cos (2*pi/15) = cos(2*(pi/15)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  },
  rw this,
  have : sqrt(3)  =  tan(pi/3),
  {
  rw tan_pi_div_three,
  },
  rw this,
  have : tan(pi/15) - tan(pi/3)  =  sin(-4*pi/15)/(cos(pi/15)*cos(pi/3)),
  {
  rw tan_sub_tan',
  have : sin((pi/15) - (pi/3)) = sin (-4*pi/15),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  repeat {assumption},
  },
  rw this,
  have : sin((-4)*π/15)/(cos(π/15)*cos(π/3))/(cos(2*π/15)*sin(π/15)) = sin((-4)*π/15)/(sin(π/15)*cos(π/15)*cos(π/3)*cos(2*π/15)),
  {
  field_simp,
  left,
  ring,
  },
  rw this,
  have : sin(pi/15)*cos(pi/15) = sin(2*pi/15)/2,
  {
  have : sin(2*pi/15) = 2*sin(pi/15)*cos(pi/15),
  {
  have : sin (2*pi/15) = sin(2*(pi/15)),
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
  have : sin(2*π/15)/2*cos(π/3)*cos(2*π/15) = sin(2*π/15)*cos(2*π/15)/2*cos(π/3),
  {
  ring,
  },
  rw this,
  have : sin(2*pi/15)*cos(2*pi/15) = sin(4*pi/15)/2,
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
  have : sin(-4*pi/15)  =  -sin(4*pi/15),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-4*pi/15) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  field_simp,
  ring_exp,
end

lemma Trigo_6_415_NIFN (h0 : cos(pi/9) ≠ 0) : (-sin(pi/9) + 2*cos(pi/18))/cos(pi/9)=sqrt(3):=
begin
  have : cos(pi/18)  =  sin(4*pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(4*pi/9)  =  sin(pi/9)*cos(pi/3) + sin(pi/3)*cos(pi/9),
  {
  have : sin(4*pi/9) = sin((pi/3) + (pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
  },
  rw this,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  field_simp,
  ring_exp,
end

lemma Trigo_6_416_ZILP (h0 : cos(pi/10) ≠ 0) (h1 : sin(2*pi/5) ≠ 0) : sin(7*pi/30) + sin(3*pi/10) - cos(pi/15)=1/2:=
begin
  have : sin(7*pi/30)  =  cos(4*pi/15),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/30) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw ← sub_add_eq_add_sub,
  have : cos(4*pi/15) - cos(pi/15)  =  -2*sin(pi/10)*sin(pi/6),
  {
  rw cos_sub_cos,
  have : sin(((4*pi/15) + (pi/15))/2) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((4*pi/15) - (pi/15))/2) = sin(pi/10),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw sin_pi_div_six,
  have : sin(3*pi/10)  =  -4*sin(pi/10)**3 + 3*sin(pi/10),
  {
  have : sin (3*pi/10) = sin(3*(pi/10)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_three_mul,
  ring,
  },
  rw this,
  have : (-2)*sin(π/10)*(1/2) + ((-4)*sin(π/10)**3 + 3*sin(π/10))  =  2*sin(pi/10)*(1 - 2*sin(pi/10)**2),
  {
  ring_exp,
  },
  rw this,
  have : 1 - 2*sin(pi/10)**2  =  cos(pi/5),
  {
  have : cos (pi/5) = cos(2*(pi/10)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  },
  rw this,
  have : sin(pi/10)  =  sin(pi/5)/(2*cos(pi/10)),
  {
  have : sin (pi/5) = sin(2*(pi/10)),
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
  have : 2*(sin(π/5)/(2*cos(π/10)))*cos(π/5) = 2*(sin(π/5)*cos(π/5))/(2*cos(π/10)),
  {
  ring,
  },
  rw this,
  have : sin(pi/5)*cos(pi/5)  =  sin(2*pi/5)/2,
  {
  have : sin(2*pi/5) = 2*sin(pi/5)*cos(pi/5),
  {
  have : sin (2*pi/5) = sin(2*(pi/5)),
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
  have : cos(pi/10)  =  sin(2*pi/5),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/10) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_6_417_SNCF (h0 : cos(pi/3) ≠ 0) (h1 : cos(pi/15) ≠ 0) (h2 : sin(pi/15) ≠ 0) (h3 : cos(2*pi/15) ≠ 0) (h4 : sin(4*pi/15) ≠ 0) : (sqrt(3)*tan(pi/15) - 3)/((4*cos(pi/15)**2 - 2)*sin(pi/15))=-4*sqrt(3):=
begin
  have : 4*cos(pi/15)**2 -2  =  2*cos(2*pi/15),
  {
  have : cos(2*pi/15) = 2*cos(pi/15)**2 - 1,
  {
  have : cos (2*pi/15) = cos(2*(pi/15)),
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
  have : sqrt(3)*tan(pi/15) -3  =  -sqrt(3)*(-tan(pi/15) + sqrt(3)),
  {
  ring_exp,
  rw sq_sqrt,
  ring_exp,
  linarith,
  },
  rw this,
  have : sqrt(3)  =  tan(pi/3),
  {
  field_simp,
  },
  rw this,
  have : -tan(pi/15) + tan(pi/3)  =  sin(4*pi/15)/(cos(pi/15)*cos(pi/3)),
  {
  rw neg_add_eq_sub,
  rw tan_sub_tan',
  have : sin((pi/3) - (pi/15)) = sin (4*pi/15),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  field_simp,
  repeat {assumption},
  },
  rw this,
  have : -tan(π/3)*(sin(4*π/15)/(cos(π/15)*cos(π/3)))/(2*cos(2*π/15)*sin(π/15)) = -tan(π/3)*sin(4*π/15)/(2*sin(π/15)*cos(π/15)*cos(2*π/15)*cos(π/3)),
  {
  field_simp,
  ring,
  },
  rw this,
  have : 2*sin(pi/15)*cos(pi/15) = sin(2*pi/15),
  {
  have : sin (2*pi/15) = sin(2*(pi/15)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : sin(2*pi/15)*cos(2*pi/15) = sin(4*pi/15)/2,
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
  rw tan_pi_div_three,
  rw cos_pi_div_three,
  field_simp,
  ring_exp,
end

lemma Trigo_6_418_BATW (h0 : cos(pi/9) ≠ 0) : 4*sin(pi/9) + tan(pi/9)=sqrt(3):=
begin
  rw tan_eq_sin_div_cos,
  have : 4*sin(pi/9) + sin(pi/9)/cos(pi/9)  =  (sin(pi/9) + 4*sin(pi/9)*cos(pi/9))/cos(pi/9),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw mul_assoc,
  have : sin(pi/9)*cos(pi/9)  =  sin(2*pi/9)/2,
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
  have : sin(2*pi/9)  =  -sin(pi/9)*cos(pi/3) + sin(pi/3)*cos(pi/9),
  {
  have : sin(2*pi/9) = sin((pi/3) - (pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_6_419_RVIC (h0 : 4 ≠ 0) (h1 : cos(pi/9) ≠ 0) : sin(pi/9) + tan(pi/9)/4=sqrt(3)/4:=
begin
  rw tan_eq_sin_div_cos,
  have : sin(π/9) + sin(π/9) / cos(π/9)/4  =  (sin(pi/9) + 4*sin(pi/9)*cos(pi/9))/(4*cos(pi/9)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw mul_assoc,
  have : sin(pi/9)*cos(pi/9)  =  sin(2*pi/9)/2,
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
  have : sin(2*pi/9)  =  -sin(pi/9)*cos(pi/3) + sin(pi/3)*cos(pi/9),
  {
  have : sin(2*pi/9) = sin((pi/3) - (pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_6_420_EELP (h0 : cos(4*pi/9) ≠ 0) (h1 : 3-cos(pi/9) ≠ 0) : (3 - sin(7*pi/18))*(-4*cos(pi/18) + tan(4*pi/9))/(2 - cos(pi/18)**2)=2*sqrt(3):=
begin
  have : cos(pi/18)**2  =  cos(pi/9)/2 + 1/2,
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
  have : sin(7*pi/18)  =  cos(pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : 2 - (cos(π/9)/2 + 1/2) = 3/2 - cos(pi/9)/2,
  {
  ring,
  },
  rw this,
  have : (3 - cos(π/9))*((-4)*cos(π/18) + tan(4*π/9))/(3/2 - cos(pi/9)/2) = (3 - cos(π/9))/(3/2 - cos(π/9)/2)*(-4*cos(π/18) + tan(4*π/9)),
  {
  field_simp,
  ring,
  },
  rw this,
  have : (3 - cos(pi/9))/(3/2 - cos(pi/9)/2)  =  2,
  {
  have : 3/2 - cos(pi/9)/2 = (3 - cos(pi/9))/2,
  {
  ring,
  },
  rw this,
  field_simp,
  ring,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  have : -4*cos(pi/18) + sin(4*pi/9)/cos(4*pi/9)  =  (-4*cos(pi/18)*cos(4*pi/9) + sin(4*pi/9))/cos(4*pi/9),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
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
  rw mul_assoc,
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
  have : sin(pi/9)  =  -sin(pi/3)*cos(4*pi/9) + sin(4*pi/9)*cos(pi/3),
  {
  have : sin(pi/9) = sin((4*pi/9) - (pi/3)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_6_421_URXJ (h0 : cos(pi/9) ≠ 0) : 4*sin(pi/9) + tan(pi/9)=sqrt(3):=
begin
  rw tan_eq_sin_div_cos,
  have : 4*sin(pi/9) + sin(pi/9)/cos(pi/9) =  (sin(pi/9) + 4*sin(pi/9)*cos(pi/9))/cos(pi/9),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw mul_assoc,
  have : sin(pi/9)*cos(pi/9)  =  sin(2*pi/9)/2,
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
  have : sin(2*pi/9)  =  -sin(pi/9)*cos(pi/3) + sin(pi/3)*cos(pi/9),
  {
  have : sin(2*pi/9) = sin((pi/3) - (pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_6_422_EEVG : sin(-5*pi/36)**2 - sin(-5*pi/36)*cos(11*pi/36) + cos(11*pi/36)**2=3/4:=
begin
  have : sin(-5*pi/36)  =  -sin(5*pi/36),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-5*pi/36) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw neg_sq,
  have : sin(5*pi/36)**2  =  1/2 - cos(5*pi/18)/2,
  {
  have : cos (5*pi/18) = cos(2*(5*pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(11*pi/36)**2  =  cos(11*pi/18)/2 + 1/2,
  {
  have : cos (11*pi/18) = cos(2*(11*pi/36)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  ring,
  },
  rw this,
  rw neg_mul,
  have : sin(5*pi/36)*cos(11*pi/36)  =  sin(-pi/6)/2 + sin(4*pi/9)/2,
  {
  rw sin_mul_cos,
  have : sin((5*pi/36) + (11*pi/36)) = sin (4*pi/9),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((5*pi/36) - (11*pi/36)) = sin (-pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  rw sub_neg_eq_add,
  have : 1/2 - cos(5*π/18)/2 + (sin(-π/6)/2 + sin(4*π/9)/2) + (cos(11*π/18)/2 + 1/2) = 1 + (-cos(5*π/18)/2 + cos(11*π/18)/2) + (sin(-π/6)/2 + sin(4*π/9)/2),
  {
  ring,
  },
  rw this,
  have : -cos(5*pi/18)/2 + cos(11*pi/18)/2  =  sin(-pi/6)*sin(4*pi/9),
  {
  have : cos(5*pi/18) - cos(11*pi/18) = -2*sin(-pi/6)*sin(4*pi/9),
  {
  rw cos_sub_cos,
  have : sin(((5*pi/18) + (11*pi/18))/2) = sin (4*pi/9),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((5*pi/18) - (11*pi/18))/2) = sin(-pi/6),
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
  field_simp,
  ring_exp,
end

lemma Trigo_6_423_MYOI (h0 : 1 - tan(pi/10) * tan(7*pi/30) ≠ 0) (h1 : cos(pi/10) ≠ 0) (h2 : cos(7*pi/30) ≠ 0) (h3 : tan(pi/10) ≠ 0) (h4 : tan(7*pi/30) ≠ 0) (h5: sqrt 3 ≠ 0) : (tan(pi/10) + tan(7*pi/30) + tan(2*pi/3))/(tan(pi/10)*tan(7*pi/30)*tan(pi/3))=-1:=
begin
  have : tan(pi/10) + tan(7*pi/30)  =  (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3),
  {
  rw tan_add_tan,
  have : tan((pi/10) + (7*pi/30)) = tan (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  have : tan(2*pi/3)  =  -tan(pi/3),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (2*pi/3) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : (-tan(pi/10)*tan(7*pi/30) + 1)*tan(pi/3)  =  -tan(pi/10)*tan(7*pi/30)*tan(pi/3) + tan(pi/3),
  {
  ring_exp,
  },
  rw this,
  field_simp,
end

lemma Trigo_6_424_JQLY (h0 : sin(pi/36) ≠ 0) (h1 : cos(pi/36) ≠ 0) (h2 : sin(pi/18) ≠ 0) (h3 : cos(pi/18) ≠ 0) : (tan(pi/36) - 1/tan(pi/36))*cos(7*pi/18)/(sin(7*pi/18) + 1)=-2:=
begin
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  have : sin(pi/36)/cos(pi/36) - cos(pi/36)/sin(pi/36)  =  (-cos(pi/36)**2 + sin(pi/36)**2)/(sin(pi/36)*cos(pi/36)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq, -sin_pi_div_three, -cos_pi_div_three],
  ring_exp,
  },
  rw this,
  have : -cos(pi/36)**2 + sin(pi/36)**2  =  -cos(pi/18),
  {
  have : cos(pi/18) = -sin(pi/36)**2 + cos(pi/36)**2,
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
  linarith,
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
  have : cos(7*pi/18)  =  sin(pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(pi/9)  =  2*sin(pi/18)*cos(pi/18),
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
  have : sin(7*pi/18)  =  cos(pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (7*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(pi/9) + 1  =  2*cos(pi/18)**2,
  {
  have : cos(pi/18)**2 = cos(pi/9)/2 + 1/2,
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
  linarith,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_6_425_MXKD (h0 : sin(x) ≠ 0) (h1 : 1 - cos(x) ≠ 0) : sin(x)/(1 - cos(x))-(1+cos(x))/sin(x)=0:=
begin
  have : sin(x)/(1 - cos(x)) - (1 + cos(x))/sin(x)  =  (sin(x)**2 - (1 - cos(x))*(cos(x) + 1))/((1 - cos(x))*sin(x)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : (1 - cos(x))*(cos(x) + 1)  =  1 - cos(x)**2,
  {
  ring_exp,
  },
  rw this,
  have : sin x ** 2 - (1 - cos x ** 2) = sin x ** 2 + cos x ** 2 - 1,
  {
  ring,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  norm_num,
end

lemma Trigo_6_426_ANRK (h0 : sin(x) ≠ 0) : -2*cos(x + y) + sin(2*x + y)/sin(x)-sin(y)/sin(x)=0:=
begin
  rw sub_eq_add_neg,
  rw add_right_comm,
  rw add_assoc,
  rw ← neg_div,
  have : -sin(y)/sin(x) + sin(2*x + y)/sin(x)  =  (-sin(y) + sin(2*x + y))/sin(x),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : -sin(y) + sin(2*x + y)  =  2*sin(x)*cos(x + y),
  {
  rw neg_add_eq_sub,
  rw sin_sub_sin,
  have : cos(((2*x + y) + (y))/2) = cos (x + y),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin(((2*x + y) - (y))/2) = sin(x),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_6_427_VHTP (h0 : sin(7*pi/18) ≠ 0) : (-sin(pi/9) + 2*cos(pi/18))/sin(7*pi/18)=sqrt(3):=
begin
  have : cos(pi/18)  =  sin(pi/9)*sin(pi/6) + cos(pi/9)*cos(pi/6),
  {
  have : cos(pi/18) = cos((pi/6) - (pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_sub,
  ring,
  },
  rw this,
  rw sin_pi_div_six,
  have : cos(pi/9)  =  sin(7*pi/18),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/9) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  field_simp,
  ring_exp,
end
