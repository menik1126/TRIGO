import trigo_import
open real
open_locale real
variables (x y : ℝ)

lemma Trigo_2_100_EZFL : -sqrt(3)*sin(25*pi/6)**2 - sin(25*pi/6)*cos(25*pi/6)=-sqrt(3)/2:=
begin
  have : sin(25*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_add_int_mul_two_pi (25*pi/6) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(25*pi/6)  =  cos(pi/6),
  {
  rw cos_eq_cos_add_int_mul_two_pi (25*pi/6) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  rw cos_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_101_VKRO : sin(pi/12)*cos(5*pi/12) + sin(7*pi/12)*cos(pi/12)=1:=
begin
  have : sin(pi/12)*cos(5*pi/12)  =  -sin(pi/3)/2 + sin(pi/2)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((5*pi/12) + (pi/12)) = sin (pi/2),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((5*pi/12) - (pi/12)) = sin (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(7*pi/12)*cos(pi/12)  =  sin(2*pi/3)/2 + sin(pi/2)/2,
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
  have : sin(2*pi/3)  =  sin(pi/3),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_two,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_102_XATR : -sin(pi/12)**2 + cos(-pi/12)**2=sqrt(3)/2:=
begin
  have : cos(-pi/12)  =  cos(pi/12),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : -sin(pi/12)**2 + cos(pi/12)**2  =  cos(pi/6),
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
  rw cos_pi_div_six,
end

lemma Trigo_2_103_PTKE : 2*sin(pi/4)*cos(pi/4) + cos(pi/2)=1:=
begin
  have : 2*sin(pi/4)*cos(pi/4)  =  sin(pi/2),
  {
  have : sin (pi/2) = sin(2*(pi/4)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  rw cos_pi_div_two,
  rw sin_pi_div_two,
  norm_num,
end

lemma Trigo_2_104_GLWU : -sin(pi/12)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12)=sqrt(3)/2:=
begin
  have : -sin(pi/12)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12)  =  sin(pi/3),
  {
  have : sin(pi/3) = sin((5*pi/12) - (pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  rw sin_pi_div_three,
end

lemma Trigo_2_105_DEZF : 1 - sin(25*pi/6)**2=3/4:=
begin
  have : sin(25*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_add_int_mul_two_pi (25*pi/6) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_2_106_JRSX : 2*sin(5*pi/12)*cos(5*pi/12)=1/2:=
begin
  have : 2*sin(5*pi/12)*cos(5*pi/12)  =  sin(5*pi/6),
  {
  have : sin (5*pi/6) = sin(2*(5*pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  have : sin(5*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
end

lemma Trigo_2_107_FWSU : sin(17*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(17*pi/180)=sqrt(3)/2:=
begin
  have : sin(17*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(17*pi/180)  =  sin(pi/3),
  {
  have : sin(pi/3) = sin((17*pi/180) + (43*pi/180)),
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

lemma Trigo_2_108_CKZV : sin(-31*pi/6)=1/2:=
begin
  have : sin(-31*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-31*pi/6) (-3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
end

lemma Trigo_2_109_GAYY : sin(pi/8)*cos(pi/8)=sqrt(2)/4:=
begin
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
  rw sin_pi_div_four,
  field_simp,
  ring_exp,
end

lemma Trigo_2_110_VRLM : (2*sin(-29*pi/6)*cos(41*pi/6) - sin(-13*pi/3))/(sin(-35*pi/6)**2 - cos(-16*pi/3) - cos(-29*pi/6)**2 + 1)=sqrt(3):=
begin
  have : sin(-13*pi/3)  =  -sin(pi/3),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-13*pi/3) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-29*pi/6)  =  -sin(pi/6),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-29*pi/6) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(41*pi/6)  =  -cos(pi/6),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (41*pi/6) (3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-29*pi/6)  =  -cos(pi/6),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-29*pi/6) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-35*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_add_int_mul_two_pi (-35*pi/6) (3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-16*pi/3)  =  -cos(pi/3),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-16*pi/3) (-3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  rw cos_pi_div_six,
  rw sin_pi_div_three,
  rw cos_pi_div_three,
  norm_num,
end

lemma Trigo_2_111_AOAD : sin(pi/5)*sin(7*pi/15) + cos(pi/5)*cos(8*pi/15)=1/2:=
begin
  have : cos(pi/5)*cos(8*pi/15)  =  cos(11*pi/15)/2 + cos(pi/3)/2,
  {
  rw mul_comm,
  rw cos_mul_cos,
  have : cos((8*pi/15) + (pi/5)) = cos (11*pi/15),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((8*pi/15) - (pi/5)) = cos (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(pi/5)*sin(7*pi/15)  =  -cos(2*pi/3)/2 + cos(4*pi/15)/2,
  {
  rw mul_comm,
  rw sin_mul_sin,
  have : cos((7*pi/15) + (pi/5)) = cos (2*pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((7*pi/15) - (pi/5)) = cos (4*pi/15),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : cos(11*pi/15)  =  -cos(4*pi/15),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (11*pi/15) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(2*pi/3)  =  -cos(pi/3),
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

lemma Trigo_2_112_CUYK : sin(4*pi/3) - sin(5*pi/2) + cos(25*pi/6) + tan(9*pi/4)=0:=
begin
  have : sin(5*pi/2)  =  sin(pi/2),
  {
  rw sin_eq_sin_add_int_mul_two_pi (5*pi/2) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(4*pi/3)  =  -sin(pi/3),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (4*pi/3) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(25*pi/6)  =  cos(pi/6),
  {
  rw cos_eq_cos_add_int_mul_two_pi (25*pi/6) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(9*pi/4)  =  tan(pi/4),
  {
  rw tan_eq_tan_add_int_mul_pi (9*pi/4) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_two,
  rw sin_pi_div_three,
  rw cos_pi_div_six,
  rw tan_pi_div_four,
  field_simp,
  ring_exp,
end

lemma Trigo_2_113_GCGI : 1/2 - cos(pi/12)**2=-sqrt(3)/4:=
begin
  have : cos(pi/12)**2  =  cos(pi/6)/2 + 1/2,
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
  field_simp,
  ring_exp,
end

lemma Trigo_2_114_VFFU : -sin(pi/12)*cos(pi/3) + sin(5*pi/12)*cos(pi/6)=sqrt(2)/2:=
begin
  have : sin(5*pi/12)  =  cos(pi/12),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(pi/3)  =  sin(pi/6),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : -sin(pi/12)*sin(pi/6) + cos(pi/12)*cos(pi/6)  =  cos(pi/4),
  {
  have : cos(pi/4) = cos((pi/6) + (pi/12)),
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
end

lemma Trigo_2_115_FOXM : sin(pi/9)*cos(2*pi/9) + sin(2*pi/9)*cos(pi/9)=sqrt(3)/2:=
begin
  have : sin(pi/9)*cos(2*pi/9) + sin(2*pi/9)*cos(pi/9)  =  sin(pi/3),
  {
  have : sin(pi/3) = sin((pi/9) + (2*pi/9)),
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

lemma Trigo_2_116_GRUD : (-sin(pi/12) + cos(pi/12))*(sin(pi/12) + cos(pi/12))=sqrt(3)/2:=
begin
  have : (-sin(pi/12) + cos(pi/12))*(sin(pi/12) + cos(pi/12))  =  -sin(pi/12)**2 + cos(pi/12)**2,
  {
  ring_exp,
  },
  rw this,
  have : -sin(pi/12)**2 + cos(pi/12)**2  =  cos(pi/6),
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
  rw cos_pi_div_six,
end

lemma Trigo_2_117_ZIKP : sin(pi/12)*cos(5*pi/12) + sin(7*pi/12)*cos(pi/12)=1:=
begin
  have : sin(7*pi/12)  =  sin(5*pi/12),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (7*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(pi/12)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12)  =  sin(pi/2),
  {
  have : sin(pi/2) = sin((pi/12) + (5*pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
  },
  rw this,
  rw sin_pi_div_two,
end

lemma Trigo_2_118_YDUQ : (sin(-29*pi/6)*cos(41*pi/6) - 2*cos(-29*pi/6))/(sin(-35*pi/6)**2 + sin(41*pi/6) + cos(-29*pi/6)**2 + 1)=sqrt(3)/2:=
begin
  have : sin(-29*pi/6)  =  -sin(pi/6),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-29*pi/6) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(41*pi/6)  =  -cos(pi/6),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (41*pi/6) (3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-29*pi/6)  =  -cos(pi/6),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-29*pi/6) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-35*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_add_int_mul_two_pi (-35*pi/6) (3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(41*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (41*pi/6) (3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  rw cos_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_119_HTCH : -sin(-x + pi/4) + sin(x + pi/4)=sqrt(2)*sin(x):=
begin
  have : sin(-x + pi/4)  =  -sin(x)*cos(pi/4) + sin(pi/4)*cos(x),
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
  rw cos_pi_div_four,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_120_VMXM : tan(pi/6)/(1 - tan(pi/6)**2)=sqrt(3)/2:=
begin
  rw tan_pi_div_six,
  norm_num,
  field_simp,
end

lemma Trigo_2_121_OABC : -sin(25*pi/6)**2 + sin(25*pi/6)*cos(25*pi/6)=sqrt(3)/4-1/4:=
begin
  have : sin(25*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_add_int_mul_two_pi (25*pi/6) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(25*pi/6)  =  cos(pi/6),
  {
  rw cos_eq_cos_add_int_mul_two_pi (25*pi/6) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(pi/6)**2  =  1/2 - cos(pi/3)/2,
  {
  have : cos (pi/3) = cos(2*(pi/6)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : sin(pi/6)*cos(pi/6)  =  sin(pi/3)/2,
  {
  have : sin(pi/3) = 2*sin(pi/6)*cos(pi/6),
  {
  have : sin (pi/3) = sin(2*(pi/6)),
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
  rw sin_pi_div_three,
  rw cos_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_2_122_VHED : (3*sin(-x - pi) + sin(x + pi/2))/(-cos(-x + 5*pi) + 2*cos(-x + 11*pi/2))=(cos(x)+3*sin(x))/(-2*sin(x)+cos(x)):=
begin
  have : sin(-x - pi)  =  sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-x - pi) (-1),
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
  have : cos(-x + 5*pi)  =  -cos(x),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-x + 5*pi) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-x + 11*pi/2)  =  -sin(x),
  {
  rw cos_eq_neg_sin_neg_add_pi_div_two_add_int_mul_two_pi_add_pi (-x + 11*pi/2) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  ring_exp,
end

lemma Trigo_2_123_WEDB : sin(x - pi/6)**2 + sin(x + pi/3)**2=1:=
begin
  have : sin(x - pi/6)**2  =  1/2 - cos(2*x - pi/3)/2,
  {
  have : cos (2*x - pi/3) = cos(2*(x - pi/6)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : sin(x + pi/3)**2  =  1/2 - cos(2*x + 2*pi/3)/2,
  {
  have : cos (2*x + 2*pi/3) = cos(2*(x + pi/3)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(2*x + 2*pi/3)  =  -cos(2*x - pi/3),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (2*x + 2*pi/3) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  field_simp,
  ring_exp,
end

lemma Trigo_2_124_VKAO : sin(pi/12)*cos(5*pi/12) + sin(7*pi/12)*cos(pi/12)=1:=
begin
  have : sin(7*pi/12)  =  sin(5*pi/12),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (7*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(pi/12)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12)  =  sin(pi/2),
  {
  have : sin(pi/2) = sin((pi/12) + (5*pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
  },
  rw this,
  rw sin_pi_div_two,
end

lemma Trigo_2_125_NXBJ (h0 : cos(pi/20) ≠ 0) (h1 : cos(17*pi/60) ≠ 0) : (tan(pi/20) + tan(17*pi/60))/(-tan(pi/20)*tan(17*pi/60) + 1)=sqrt(3):=
begin
  have : (tan(pi/20) + tan(17*pi/60))/(-tan(pi/20)*tan(17*pi/60) + 1)  =  tan(pi/3),
  {
  have : tan(pi/3) = tan((pi/20) + (17*pi/60)),
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
end

lemma Trigo_2_126_AKLW (h0 : cos(x) + cos(2*x) ≠ 0) (h1 : cos(3*x/2) ≠ 0) (h2 : cos(x/2) ≠ 0) (h3 : cos(x)/2 + cos(2*x)/2 ≠ 0) : -tan(x/2) + tan(3*x/2)=2*sin(x)/(cos(x)+cos(2*x)):=
begin
  have : -tan(x/2) + tan(3*x/2)  =  sin(x)/(cos(x/2)*cos(3*x/2)),
  {
  rw neg_add_eq_sub,
  rw tan_sub_tan',
  have : sin((3*x/2) - (x/2)) = sin (x),
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
  have : cos(x/2)*cos(3*x/2) = cos(x)/2 + cos(2*x)/2,
  {
  rw mul_comm,
  rw cos_mul_cos,
  have : cos((3*x/2) + (x/2)) = cos (2*x),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((3*x/2) - (x/2)) = cos (x),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  have : sin(x)/(cos(x)/2 + cos(2*x)/2)  =  2*sin(x)/(cos(x) + cos(2*x)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
end

lemma Trigo_0_127_ZUNT (h0 : cos(x)**2 ≠ 0) : -sin(x)**5/cos(x)**2 + sin(x)*cos(x)**2 - 2*sin(x) + sin(x)/cos(x)**2=0:=
begin
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
  rw sub_eq_add_neg,
  rw add_assoc,
  rw ← sub_eq_neg_add (sin x / cos x ** 2) (2 * sin x),
  rw ← add_sub_assoc,
  have : (-sin(x)**2 + cos(x)**2)*sin(x)/cos(x)**2 + sin(x)/cos(x)**2  =  ((-sin(x)**2 + cos(x)**2)*sin(x) + sin(x))/cos(x)**2,
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  have : (-sin(x)**2 + cos(x)**2)*sin(x) + sin(x)  =  (-sin(x)**2 + cos(x)**2 + 1)*sin(x),
  {
  ring_exp,
  },
  rw this,
  rw sin_sq,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_128_ESIQ : sin(pi/12)**2 + sin(pi/12)*cos(5*pi/12) + cos(5*pi/12)**2=3/2 - 3*sqrt(3)/4:=
begin
  have : cos(5*pi/12)  =  sin(pi/12),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  ring_nf,
  have : sin(pi/12)**2  =  1/2 - cos(pi/6)/2,
  {
  have : cos (pi/6) = cos(2*(pi/12)),
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
  field_simp,
  ring_exp,
end

lemma Trigo_0_129_COJG (h0 : sin(pi/12) ≠ 0) (h1 : cos(pi/12) ≠ 0) : -(2*sin(pi/24)**2 - 1)/(sin(pi/24)*cos(pi/24)) + 2*tan(pi/12)=8:=
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
  rw tan_eq_sin_div_cos,
  have : 2*sin(pi/24)**2 - 1  =  -cos(pi/12),
  {
  have : cos(pi/12) = 1 - 2*sin(pi/24)**2,
  {
  have : cos (pi/12) = cos(2*(pi/24)),
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
  rw neg_neg,
  have : cos (π/12)/(sin(π/12)/2) = 2*cos(π/12)/sin (π/12),
  {
    field_simp,
    ring,
  },
  rw this,
  have :2*cos(pi/12)/sin(pi/12) + 2*(sin(pi/12)/cos(pi/12)) =  (2*sin(pi/12)**2 + 2*cos(pi/12)**2)/(sin(pi/12)*cos(pi/12)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  have : 2*sin(pi/12)**2 + 2*cos(pi/12)**2  =  2,
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

lemma Trigo_0_130_UBYA (h0 : sin(x) ≠ 0)  (h1 : tan(x) ≠ 0) : sin(pi - x)*cos(-x + 2*pi)*tan(-x - pi)*tan(-x + 3*pi/2)/sin(-x - pi)=-cos(x):=
begin
  have : sin(pi - x)  =  sin(x),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (pi - x) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-x + 2*pi)  =  cos(-x),
  {
  rw cos_eq_cos_add_int_mul_two_pi (-x + 2*pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  have : cos(-x)  =  cos(x),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-x) (0),
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
  have : sin(-x - pi)  =  -sin(x + pi),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-x - pi) (0),
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
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_131_OLPJ (h0 : cos(x)**2 ≠ 0) : (cos(2*x) + 1)*(tan(x)**2 + 1)=2:=
begin
  have : cos(2*x)  =  2*cos(x)**2 - 1,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_two_mul,
  },
  rw this,
  rw tan_eq_sin_div_cos,
  field_simp,
end

lemma Trigo_0_132_YSVW : sin(1)**2 + cos(1)**2=1:=
begin
  rw sin_sq_add_cos_sq,
end

lemma Trigo_0_133_SMIB (h0 : sin(pi/9) ≠ 0) : cos(pi/9)*cos(2*pi/9)*cos(4*pi/9)=1/8:=
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
  rw div_mul_eq_mul_div,
  rw this,
  rw div_mul_eq_mul_div,
  rw div_mul_eq_mul_div,
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
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_134_OSKG : sin(pi/12)*cos(5*pi/12) - sin(5*pi/12)*cos(pi/12)=-sqrt(3)/2:=
begin
  have : sin(pi/12)*cos(5*pi/12) - sin(5*pi/12)*cos(pi/12) = sin(-pi/3),
  {
  have : sin(-pi/3) = sin((pi/12) - (5*pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_sub,
  ring,
  },
  rw this,
  have : sin(-pi/3)  =  -sin(pi/3),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
  field_simp,
end

lemma Trigo_0_135_AVUS (h0 : sin(pi/12) ≠ 0) (h1 : cos(pi/12) ≠ 0) : tan(pi/12) + 1/tan(pi/12)=4:=
begin
  rw tan_eq_sin_div_cos,
  rw one_div_div,
  have : sin(pi/12)/cos(pi/12) + cos(pi/12)/sin(pi/12)  =  (sin(pi/12)**2 + cos(pi/12)**2)/(sin(pi/12)*cos(pi/12)),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
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

lemma Trigo_0_136_TRLV : sin(pi/12)*cos(11*pi/12)=-1/4:=
begin
  have : cos(11*pi/12)  =  -cos(pi/12),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (11*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_neg,
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

lemma Trigo_0_137_ZVTE (h0: sin(x) ≠ 0) (h1: cos(x) ≠ 0) : tan(x)=(1-cos(2*x))/sin(2*x):=
begin
  have : cos(2*x)  =  1 - 2*sin(x)**2,
  {
  have : cos (2*x) = cos(2*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_two_mul'',
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
  rw tan_eq_sin_div_cos,
  field_simp,
  ring,
end

lemma Trigo_0_138_GYRF : sin(13*pi/180)*cos(137*pi/180) + cos(13*pi/180)*cos(47*pi/180)=1/2:=
begin
  have : cos(47*pi/180)  =  sin(137*pi/180),
  {
  rw cos_eq_sin_add_pi_div_two_add_int_mul_two_pi (47*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw add_comm,
  rw mul_comm,
  have : sin(137*pi/180)*cos(13*pi/180) + sin(13*pi/180)*cos(137*pi/180)  =  sin(5*pi/6),
  {
  have : sin(5*pi/6) = sin((13*pi/180) + (137*pi/180)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_add,
  ring,
  },
  rw this,
  have : sin(5*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
end

lemma Trigo_0_139_FGHY : (sin(pi/12) + cos(pi/12))**2=3/2:=
begin
  have : (sin(pi/12) + cos(pi/12))**2  =  sin(pi/12)**2 + 2*sin(pi/12)*cos(pi/12) + cos(pi/12)**2,
  {
  ring_exp,
  },
  rw this,
  rw add_right_comm,
  rw sin_sq_add_cos_sq,
  have : 2*sin(pi/12)*cos(pi/12)  =  sin(pi/6),
  {
  have : sin (pi/6) = sin(2*(pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw sin_two_mul,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_0_140_QAXJ : sqrt(3)*sin(2*pi/3) + cos(pi/3)=2:=
begin
  have : sin(2*pi/3)  =  sin(pi/3),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  ring_exp,
  rw sq_sqrt,
  norm_num,
  repeat {linarith},
end

lemma Trigo_0_141_BVJX (h0 : cos(x)**2 ≠ 0) : (tan(x)**2 + 1)*cos(x)**2=1:=
begin
  rw tan_eq_sin_div_cos,
  rw div_pow,
  have : (sin(x)**2/cos(x)**2 + 1)*cos(x)**2  =  sin(x)**2 + cos(x)**2,
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  },
  rw this,
  rw sin_sq_add_cos_sq,
end

lemma Trigo_0_142_NHYP : cos(pi/10)*cos(7*pi/30) - cos(4*pi/15)*cos(2*pi/5)=1/2:=
begin
  have : cos(2*pi/5)  =  sin(pi/10),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (2*pi/5) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(4*pi/15)  =  sin(7*pi/30),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (4*pi/15) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw mul_comm (sin(7*π/30)) (sin(π/10)),
  have : cos(pi/10)*cos(7*pi/30) - sin(pi/10)*sin(7*pi/30) =  cos(pi/3),
  {
  have : cos(pi/3) = cos((pi/10) + (7*pi/30)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_add,
  },
  rw this,
  rw cos_pi_div_three,
end

lemma Trigo_0_143_RDGT (h0 : sin(2*pi/9) ≠ 0) (h1 : cos(pi/9) ≥ 0) : sqrt(cos(2*pi/9) + 1)*sin(pi/9)/cos(5*pi/18)=sqrt(2)/2:=
begin
  have : cos(2*pi/9)  =  2*cos(pi/9)**2 - 1,
  {
  have : cos (2*pi/9) = cos(2*(pi/9)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul,
  },
  rw this,
  simp,
  rw sqrt_sq_eq_abs,
  rw abs_eq_self.mpr h1,
  rw mul_assoc,
  rw mul_comm (cos(π/9)) (sin(π/9)),
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
  have : cos(5*pi/18)  =  sin(2*pi/9),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_144_QRGX : sin(-35*pi/6)*cos(-17*pi/3) + sin(-2*pi/3)*cos(43*pi/6)=1:=
begin
  have : sin(-35*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_add_int_mul_two_pi (-35*pi/6) (3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-17*pi/3)  =  cos(pi/3),
  {
  rw cos_eq_cos_add_int_mul_two_pi (-17*pi/3) (3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-2*pi/3)  =  -sin(pi/3),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(43*pi/6)  =  -cos(pi/6),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (43*pi/6) (-4),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  rw cos_pi_div_six,
  ring_exp,
  rw sq_sqrt,
  norm_num,
  repeat {linarith},
end

lemma Trigo_0_145_STWJ : -sin(pi/18)*cos(11*pi/36) + sin(4*pi/9)*cos(7*pi/36)=sqrt(2)/2:=
begin
  have : sin(pi/18)  =  cos(4*pi/9),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (pi/18) (0),
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
  rw neg_mul,
  rw mul_comm,
  rw ← neg_mul,
  have : -sin(7*pi/36)*cos(4*pi/9) + sin(4*pi/9)*cos(7*pi/36)  =  sin(pi/4),
  {
  have : sin(pi/4) = sin((4*pi/9) - (7*pi/36)),
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

lemma Trigo_0_146_ASIB (h0 : cos(x) ≠ 0) (h1 : tan(x) ≠ 0) : sin(-x + pi/2)*cos(-x + 2*pi)*tan(-x + 3*pi)/(sin(x + pi/2)*tan(x + pi))=-cos(x):=
begin
  have : sin(-x + pi/2)  =  cos(x),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (-x + pi/2) (0),
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
  have : tan(-x + 3*pi)  =  -tan(x),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-x + 3*pi) (3),
  repeat {apply congr_arg _},
  simp,
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
  have : tan(x + pi)  =  tan(x),
  {
  rw tan_eq_tan_add_int_mul_pi (x + pi) (-1),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_147_XWAG (h0 : cos(pi/5) ≠ 0) (h1 : cos(2*pi/15) ≠ 0) (h2 : 1 - tan(pi/5) * tan(2*pi/15) ≠ 0) : sqrt(3)*tan(2*pi/15)*tan(pi/5) + tan(2*pi/15) + tan(pi/5)=sqrt(3):=
begin
  rw add_assoc,
  have : tan(2*pi/15) + tan(pi/5)  = tan(pi/3)*(-tan(2*pi/15)*tan(pi/5) + 1),
  {
  rw add_comm,
  rw tan_add_tan,
  have : tan((pi/5) + (2*pi/15)) = tan (pi/3),
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
  have : sqrt(3)*(-tan(2*pi/15)*tan(pi/5) + 1)  =  -sqrt(3)*tan(2*pi/15)*tan(pi/5) + sqrt(3),
  {
  ring_exp,
  },
  rw this,
  norm_num,
end

lemma Trigo_0_148_KKNW (h0 : 1 - tan(pi/9) * tan(pi/18) ≠ 0) (h1 : cos(pi/18) ≠ 0) (h2 : cos(pi/9) ≠ 0) : tan(pi/18)*tan(pi/9) + tan(pi/18)*tan(pi/3) + tan(pi/9)*tan(pi/3)=1:=
begin
  rw tan_pi_div_three,
  rw add_assoc,
  have : tan(pi/18)*sqrt(3) + tan(pi/9)*sqrt(3)  =  sqrt(3)*(tan(pi/18) + tan(pi/9)),
  {
  ring_exp,
  },
  rw this,
  have : tan(pi/18) + tan(pi/9)  =  (-tan(pi/18)*tan(pi/9) + 1)*tan(pi/6),
  {
  rw add_comm,
  rw tan_add_tan,
  have : tan((pi/9) + (pi/18)) = tan (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  repeat {assumption},
  },
  rw this,
  rw tan_pi_div_six,
  ring_exp,
  rw sq_sqrt,
  norm_num,
  repeat {linarith},
end

lemma Trigo_0_149_DXJL : sin(5*pi/18)*sin(7*pi/18) + cos(11*pi/18)*cos(31*pi/18)=1/2:=
begin
  have : cos(11*pi/18)  =  -cos(7*pi/18),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (11*pi/18) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(31*pi/18)  =  cos(5*pi/18),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (31*pi/18) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw add_comm,
  rw neg_mul,
  rw mul_comm,
  rw ← neg_mul,
  have : -cos(5*pi/18)*cos(7*pi/18) + sin(5*pi/18)*sin(7*pi/18)  =  -cos(2*pi/3),
  {
  have : cos(2*pi/3) = -sin(5*pi/18)*sin(7*pi/18) + cos(5*pi/18)*cos(7*pi/18),
  {
  have : cos(2*pi/3) = cos((5*pi/18) + (7*pi/18)),
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
