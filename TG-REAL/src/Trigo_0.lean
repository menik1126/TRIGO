import trigo_import
open real
open_locale real
variables (x y : ℝ)



lemma Trigo_0_0_RLMT : 3/4 - 3*sin(pi/12)**2/2=3*sqrt(3)/8:=
begin
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

lemma Trigo_0_1_NBLH (h0 : cos(5*pi/6) ≠ 0) : 2*tan(5*pi/6)/(1 - tan(5*pi/6)**2)=-sqrt(3):=
begin
  have : 2*tan(5*pi/6)/(1 - tan(5*pi/6)**2)  =  tan(5*pi/3),
  {
  have : tan (5*pi/3) = tan(2*(5*pi/6)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw tan_two_mul,
  repeat {assumption},
  },
  rw this,
  have : tan(5*pi/3)  =  -tan(pi/3),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (5*pi/3) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_three,
end

lemma Trigo_0_2_LVJK : sin(pi/3) + 2*cos(pi/12)**2 - cos(pi/2)=sqrt(3)+1:=
begin
  rw cos_pi_div_two,
  rw sin_pi_div_three,
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
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_3_NRRR : sin(pi/3)**2 + cos(pi/6)*cos(pi/3)=(3+sqrt(3))/4:=
begin
  rw cos_pi_div_six,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_4_MQBL : sin(pi/4)*cos(pi/4)=1/2:=
begin
  rw sin_pi_div_four,
  rw cos_pi_div_four,
  field_simp,
end

lemma Trigo_0_5_QTWV : tan(3*pi/4)=-1:=
begin
  have : tan(3*pi/4)  =  -tan(pi/4),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (3*pi/4) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_four,
end

lemma Trigo_0_6_HTUW : sin(-2*pi/3)=-sqrt(3)/2:=
begin
  have : sin(-2*pi/3)  =  -sin(pi/3),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (-2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
  field_simp,
end

lemma Trigo_0_7_HOEW : sin(23*pi/6)=-1/2:=
begin
  have : sin(23*pi/6)  =  -sin(pi/6),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (23*pi/6) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_0_8_LNDY : sin(2*pi/3)=sqrt(3)/2:=
begin
  have : sin(2*pi/3)  =  sin(pi/3),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
end

lemma Trigo_0_9_PWSS : sin(pi/12)*cos(pi/12)=1/4:=
begin
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

lemma Trigo_0_10_JCYT : -sin(x)**2*sin(y)**2 - sin(x)**2*cos(y)**2 + sin(x)**2 + sin(y)**2=sin(y)**2:=
begin
  have : -sin(x)**2*sin(y)**2 - sin(x)**2*cos(y)**2  =  -sin(x)**2*(sin(y)**2 + cos(y)**2),
  {
  field_simp [-sin_sq_add_cos_sq, -cos_sq_add_sin_sq],
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
  norm_num,
end

lemma Trigo_0_11_UPWT : -sin(23*pi/180)*cos(53*pi/180) + sin(53*pi/180)*cos(23*pi/180)=1/2:=
begin
  have : -sin(23*pi/180)*cos(53*pi/180) + sin(53*pi/180)*cos(23*pi/180)  =  sin(pi/6),
  {
  have : sin(pi/6) = sin((53*pi/180) - (23*pi/180)),
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

lemma Trigo_0_12_KMNE : sin(pi/12)*cos(pi/12)/2=1/8:=
begin
  have : sin(pi/12)*cos(pi/12)/2  =  sin(pi/6)/4,
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

lemma Trigo_0_13_AURP : 2*sin(pi/3)=sqrt(3):=
begin
  rw sin_pi_div_three,
  field_simp,
  ring_exp,
end

lemma Trigo_0_14_HQRK : sin(23*pi/180)*cos(37*pi/180) + sin(37*pi/180)*cos(23*pi/180)=sqrt(3)/2:=
begin
  have : sin(23*pi/180)*cos(37*pi/180) + sin(37*pi/180)*cos(23*pi/180)  =  sin(pi/3),
  {
  have : sin(pi/3) = sin((23*pi/180) + (37*pi/180)),
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

lemma Trigo_0_15_ETRV : sin(5*pi/4) + tan(11*pi/3)=-sqrt(2)/2-sqrt(3):=
begin
  have : tan(11*pi/3)  =  tan(-pi/3),
  {
  rw tan_eq_tan_add_int_mul_pi (11*pi/3) (-4),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(5*pi/4)  =  -sin(pi/4),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (5*pi/4) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(-pi/3)  =  -tan(pi/3),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_three,
  rw sin_pi_div_four,
  field_simp,
  ring_exp,
end

lemma Trigo_0_16_ZMIB : -sin(pi/12)*sin(7*pi/12) + sin(5*pi/12)*sin(11*pi/12)=0:=
begin
  have : sin(7*pi/12)  =  cos(pi/12),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (7*pi/12) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
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
  have : sin(11*pi/12)  =  sin(pi/12),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (11*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  ring_exp,
end

lemma Trigo_0_17_FTGL : sin(-19*pi/6)=1/2:=
begin
  have : sin(-19*pi/6)  =  sin(-7*pi/6),
  {
  rw sin_eq_sin_add_int_mul_two_pi (-19*pi/6) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(-7*pi/6)  =  -sin(7*pi/6),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-7*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(7*pi/6)  =  -sin(pi/6),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/6) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_0_18_TPOC : sin(7*pi/6)=-1/2:=
begin
  have : sin(7*pi/6)  =  -sin(pi/6),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/6) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_0_19_TYCU : sin(3*pi/20)*cos(11*pi/60) + sin(11*pi/60)*cos(3*pi/20)=sqrt(3)/2:=
begin
  have : sin(3*pi/20)*cos(11*pi/60) + sin(11*pi/60)*cos(3*pi/20)  =  sin(pi/3),
  {
  have : sin(pi/3) = sin((3*pi/20) + (11*pi/60)),
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

lemma Trigo_0_20_BOHO : -sin(pi/12)*sin(5*pi/6) + sin(5*pi/12)*cos(pi/6)=sqrt(2)/2:=
begin
  have : sin(5*pi/12)  =  cos(pi/12),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
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

lemma Trigo_0_21_DDDQ : cos(9*pi/4) + tan(-11*pi/6)=(3*sqrt(2)+2*sqrt(3))/6:=
begin
  have : tan(-11*pi/6)  =  tan(pi/6),
  {
  rw tan_eq_tan_add_int_mul_pi (-11*pi/6) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_six,
  have : cos(9*pi/4)  =  cos(pi/4),
  {
  rw cos_eq_cos_add_int_mul_two_pi (9*pi/4) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_four,
  field_simp,
  ring_exp,
end

lemma Trigo_0_22_WAJU : (sin(5*pi/6) + sin(5*pi/3)**2 + 2*cos(pi/3)**3 - 3)/(cos(-pi/3) + 2*cos(4*pi/3)**2 + 2)=-1/2:=
begin
  rw cos_pi_div_three,
  have : sin(5*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  have : sin(5*pi/3)  =  -sin(pi/3),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (5*pi/3) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
  have : cos(-pi/3)  =  cos(pi/3),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  have : cos(4*pi/3)  =  -cos(pi/3),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (4*pi/3) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  norm_num,
end

lemma Trigo_0_23_YNNF : sin(pi/4)*cos(pi/4) + sqrt(3)*cos(pi/4)**2 - sqrt(3)/2=1/2:=
begin
  rw sin_pi_div_four,
  rw cos_pi_div_four,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_24_FUOI : (-sin(pi/12) + sin(5*pi/12))*(sin(pi/12) + sin(5*pi/12))=sqrt(3)/2:=
begin
  have : (-sin(pi/12) + sin(5*pi/12))*(sin(pi/12) + sin(5*pi/12))  =  -sin(pi/12)**2 + sin(5*pi/12)**2,
  {
  ring_exp,
  },
  rw this,
  have : sin(5*pi/12)**2  =  1/2 - cos(5*pi/6)/2,
  {
  have : cos (5*pi/6) = cos(2*(5*pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
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
  have : cos(5*pi/6)  =  -cos(pi/6),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_25_VFTE : 2*sin(-pi/6)=-1:=
begin
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

lemma Trigo_0_26_KHEN : sin(pi/12)**2 + sin(pi/12)*sin(5*pi/12) + sin(5*pi/12)**2=5/4:=
begin
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
  have : sin(5*pi/12)**2  =  1/2 - cos(5*pi/6)/2,
  {
  have : cos (5*pi/6) = cos(2*(5*pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : sin(pi/12)*sin(5*pi/12)  =  -cos(pi/2)/2 + cos(pi/3)/2,
  {
  rw mul_comm,
  rw sin_mul_sin,
  have : cos((5*pi/12) + (pi/12)) = cos (pi/2),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((5*pi/12) - (pi/12)) = cos (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw cos_pi_div_six,
  rw cos_pi_div_two,
  rw cos_pi_div_three,
  have : cos(5*pi/6)  =  -cos(pi/6),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_27_YBZQ : sqrt(3)*sin(x)/2 + cos(x)/2=cos(x-pi/3):=
begin
  have : cos(x - pi/3)  =  sin(pi/3)*sin(x) + cos(pi/3)*cos(x),
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
  field_simp,
end

lemma Trigo_0_28_MHBJ : -sin(13*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(13*pi/180)=1/2:=
begin
  have : -sin(13*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(13*pi/180)  =  sin(pi/6),
  {
  have : sin(pi/6) = sin((43*pi/180) - (13*pi/180)),
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

lemma Trigo_0_29_ATAD : -sin(13*pi/180)*cos(73*pi/180) + sin(73*pi/180)*cos(13*pi/180)=sqrt(3)/2:=
begin
  have : -sin(13*pi/180)*cos(73*pi/180) + sin(73*pi/180)*cos(13*pi/180)  =  sin(pi/3),
  {
  have : sin(pi/3) = sin((73*pi/180) - (13*pi/180)),
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

lemma Trigo_0_30_JBJQ : 2*sin(pi/8)**2 - cos(3*pi/4)=1:=
begin
  have : sin(pi/8)**2  =  1/2 - cos(pi/4)/2,
  {
  have : cos (pi/4) = cos(2*(pi/8)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  ring,
  },
  rw this,
  have : cos(3*pi/4)  =  -cos(pi/4),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (3*pi/4) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_31_HOMZ : sqrt(3)*sin(pi/12) + cos(pi/12)=sqrt(2):=
begin
  have : sqrt(3)*sin(pi/12)  =  2*sin(pi/12)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/12)  =  2*sin(pi/6)*cos(pi/12),
  {
  field_simp,
  },
  rw this,
  have : 2*sin(pi/12)*cos(pi/6) + 2*sin(pi/6)*cos(pi/12)  =  2*sin(pi/4),
  {
  have : sin(pi/4) = sin(pi/12)*cos(pi/6) + sin(pi/6)*cos(pi/12),
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
  linarith,
  },
  rw this,
  rw sin_pi_div_four,
  field_simp,
  ring_exp,
end

lemma Trigo_0_32_IVFV : sin(pi/15)*sin(2*pi/5) + cos(pi/15)*cos(2*pi/5)=1/2:=
begin
  have : sin(pi/15)*sin(2*pi/5) + cos(pi/15)*cos(2*pi/5)  =  cos(pi/3),
  {
  have : cos(pi/3) = cos((2*pi/5) - (pi/15)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_sub,
  ring,
  },
  rw this,
  rw cos_pi_div_three,
end

lemma Trigo_0_33_HFRQ : -sin(pi/8)**4 + cos(pi/8)**4=sqrt(2)/2:=
begin
  have : -sin(pi/8)**4 + cos(pi/8)**4  =  (-sin(pi/8)**2 + cos(pi/8)**2)*(sin(pi/8)**2 + cos(pi/8)**2),
  {
  ring_exp,
  },
  rw this,
  rw sin_sq_add_cos_sq,
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
  rw cos_pi_div_four,
  norm_num,
end

lemma Trigo_0_34_TZIF : sin(-pi/4) + cos(pi/3) + tan(pi/4)=(3-sqrt(2))/2:=
begin
  have : sin(-pi/4)  =  -sin(pi/4),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/4) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_four,
  rw cos_pi_div_three,
  rw tan_pi_div_four,
  field_simp,
  ring_exp,
end

lemma Trigo_0_35_DDKB : -sin(pi/9)*sin(2*pi/9) + cos(pi/9)*cos(2*pi/9)=1/2:=
begin
  have : -sin(pi/9)*sin(2*pi/9) + cos(pi/9)*cos(2*pi/9)  =  cos(pi/3),
  {
  have : cos(pi/3) = cos((pi/9) + (2*pi/9)),
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

lemma Trigo_0_36_ITDD : sin(-23*pi/6)=1/2:=
begin
  have : sin(-23*pi/6)  =  -sin(23*pi/6),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-23*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(23*pi/6)  =  -sin(pi/6),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (23*pi/6) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_0_37_QISN : 2*sin(pi/4)*cos(pi/12) - 1/2=sqrt(3)/2:=
begin
  have : 2*sin(pi/4)*cos(pi/12)  =  sin(pi/3) + sin(pi/6),
  {
  have : sin(pi/4)*cos(pi/12) = sin(pi/6)/2 + sin(pi/3)/2,
  {
  rw sin_mul_cos,
  have : sin((pi/4) + (pi/12)) = sin (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((pi/4) - (pi/12)) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_0_38_UBYU : 3/4 - 3*sin(pi/12)**2/2=3*sqrt(3)/8:=
begin
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

lemma Trigo_0_39_OVOT : -sin(pi/10)*cos(13*pi/30) + sin(13*pi/30)*cos(pi/10)=sqrt(3)/2:=
begin
  have : -sin(pi/10)*cos(13*pi/30) + sin(13*pi/30)*cos(pi/10)  =  sin(pi/3),
  {
  have : sin(pi/3) = sin((13*pi/30) - (pi/10)),
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

lemma Trigo_0_40_UUSW : 1 - 2*sin(pi/4)=1-sqrt(2):=
begin
  rw sin_pi_div_four,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_41_MKYG : sin(pi/12)*sin(5*pi/12)=1/4:=
begin
  have : sin(5*pi/12)  =  cos(pi/12),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (5*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
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

lemma Trigo_0_42_BTLV : sin(13*pi/180)*cos(8*pi/45) + sin(8*pi/45)*cos(13*pi/180)=sqrt(2)/2:=
begin
  have : sin(13*pi/180)*cos(8*pi/45)  =  -sin(19*pi/180)/2 + sin(pi/4)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((8*pi/45) + (13*pi/180)) = sin (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((8*pi/45) - (13*pi/180)) = sin (19*pi/180),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(8*pi/45)*cos(13*pi/180)  =  sin(19*pi/180)/2 + sin(pi/4)/2,
  {
  rw sin_mul_cos,
  have : sin((8*pi/45) + (13*pi/180)) = sin (pi/4),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((8*pi/45) - (13*pi/180)) = sin (19*pi/180),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  rw sin_pi_div_four,
  field_simp,
  ring_exp,
end

lemma Trigo_0_43_EYFQ : sin(13*pi/180)*cos(17*pi/180) + sin(17*pi/180)*cos(13*pi/180)=1/2:=
begin
  have : sin(13*pi/180)*cos(17*pi/180)  =  -sin(pi/45)/2 + sin(pi/6)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((17*pi/180) + (13*pi/180)) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((17*pi/180) - (13*pi/180)) = sin (pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(17*pi/180)*cos(13*pi/180)  =  sin(pi/45)/2 + sin(pi/6)/2,
  {
  rw sin_mul_cos,
  have : sin((17*pi/180) + (13*pi/180)) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((17*pi/180) - (13*pi/180)) = sin (pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_44_GTGQ : sin(7*pi/90)*cos(4*pi/45) + sin(4*pi/45)*cos(7*pi/90)=1/2:=
begin
  have : sin(7*pi/90)*cos(4*pi/45) + sin(4*pi/45)*cos(7*pi/90)  =  sin(pi/6),
  {
  have : sin(pi/6) = sin((4*pi/45) + (7*pi/90)),
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

lemma Trigo_0_45_DCSU : sin(5*pi/12)*cos(5*pi/12)=1/4:=
begin
  have : sin(5*pi/12)*cos(5*pi/12)  =  sin(0)/2 + sin(5*pi/6)/2,
  {
  rw sin_mul_cos,
  have : sin((5*pi/12) + (5*pi/12)) = sin (5*pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((5*pi/12) - (5*pi/12)) = sin (0),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  rw sin_five_pi_div_six,
  norm_num,
end

lemma Trigo_0_46_CPES : sin(7*pi/12)*cos(7*pi/12)=-1/4:=
begin
  have : sin(7*pi/12)*cos(7*pi/12)  =  sin(7*pi/6)/2,
  {
  have : sin(7*pi/6) = 2*sin(7*pi/12)*cos(7*pi/12),
  {
  have : sin (7*pi/6) = sin(2*(7*pi/12)),
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
  have : sin(7*pi/6)  =  -sin(pi/6),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/6) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_0_47_ZPHM : sqrt(3)*sin(2*pi/3)**2 + sin(2*pi/3)*cos(2*pi/3)=sqrt(3)/2:=
begin
  have : sin(2*pi/3)  =  sin(pi/3),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
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
  rw sin_pi_div_three,
  rw cos_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_0_48_WTBU : cos(2012*pi/3)=-1/2:=
begin
  have : cos(2012*pi/3)  =  -cos(pi/3),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2012*pi/3) (335),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  norm_num,
end

lemma Trigo_0_49_XRDQ : sin(pi/12)*cos(5*pi/4) + sin(pi/4)*cos(pi/12)=1/2:=
begin
  have : sin(pi/12)*cos(5*pi/4)  =  sin(4*pi/3)/2 - sin(7*pi/6)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((5*pi/4) + (pi/12)) = sin (4*pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((5*pi/4) - (pi/12)) = sin (7*pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  have : sin(pi/4)*cos(pi/12)  =  sin(pi/6)/2 + sin(pi/3)/2,
  {
  rw sin_mul_cos,
  have : sin((pi/4) + (pi/12)) = sin (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((pi/4) - (pi/12)) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
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
  have : sin(7*pi/6)  =  -sin(pi/6),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (7*pi/6) (-1),
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

