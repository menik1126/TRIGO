import trigo_import
open real
open_locale real
variables (x y : ℝ)

lemma Trigo_1_50_KHCO : -sin(pi/8)**2 + cos(pi/8)**2=sqrt(2)/2:=
begin
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
end

lemma Trigo_1_51_RTSR : sin(-7*pi/6) + sin(14*pi/3)**2 - cos(-11*pi/6)**2 + cos(3*pi) + tan(5*pi/4)=1/2:=
begin
  have : cos(3*pi)  =  cos(pi),
  {
  rw cos_eq_cos_add_int_mul_two_pi (3*pi) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi,
  have : cos(-11*pi/6)  =  cos(pi/6),
  {
  rw cos_eq_cos_add_int_mul_two_pi (-11*pi/6) (1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  have : sin(-7*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-7*pi/6) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  have : sin(14*pi/3)  =  sin(pi/3),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (14*pi/3) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
  have : tan(5*pi/4)  =  tan(pi/4),
  {
  rw tan_eq_tan_add_int_mul_pi (5*pi/4) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_four,
  norm_num,
end

lemma Trigo_1_52_HPRI : -sin(-x + pi/4)**2 + cos(-x + pi/4)**2=sin(2*x):=
begin
  have : -sin(-x + pi/4)**2 + cos(-x + pi/4)**2  =  cos(-2*x + pi/2),
  {
  have : cos (-2*x + pi/2) = cos(2*(-x + pi/4)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : cos(-2*x + pi/2)  =  sin(2*x),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (-2*x + pi/2) (0),
  repeat {apply congr_arg _},
  simp,
  },
  rw this,
end

lemma Trigo_1_53_VEOJ : sin(pi/12)*cos(5*pi/12) + sin(7*pi/12)*cos(pi/12)=1:=
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

lemma Trigo_1_54_UBZX : sin(5*pi/12)*cos(5*pi/12)=1/4:=
begin
  have : sin(5*pi/12)*cos(5*pi/12)  =  sin(5*pi/6)/2,
  {
  have : sin(5*pi/6) = 2*sin(5*pi/12)*cos(5*pi/12),
  {
  have : sin (5*pi/6) = sin(2*(5*pi/12)),
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
  have : sin(5*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_1_55_EVNG : 2*sin(pi/2)*cos(pi/2) - cos(pi) + 1=2:=
begin
  rw sin_pi_div_two,
  rw cos_pi_div_two,
  rw cos_pi,
  norm_num,
end

lemma Trigo_1_56_KHUD : -sin(pi/6)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/6)=sqrt(2)/2:=
begin
  have : -sin(pi/6)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/6)  =  sin(pi/4),
  {
  have : sin(pi/4) = sin((5*pi/12) - (pi/6)),
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

lemma Trigo_1_57_DCGU : tan(pi/12)=2-sqrt(3):=
begin
  rw tan_pi_div_twelve,
end

lemma Trigo_1_58_WSSW : sin(43*pi/180)*cos(167*pi/180) + cos(43*pi/180)*cos(77*pi/180)=-1/2:=
begin
  have : sin(43*pi/180)*cos(167*pi/180)  =  -sin(31*pi/45)/2 + sin(7*pi/6)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((167*pi/180) + (43*pi/180)) = sin (7*pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((167*pi/180) - (43*pi/180)) = sin (31*pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : cos(43*pi/180)*cos(77*pi/180)  =  cos(2*pi/3)/2 + cos(-17*pi/90)/2,
  {
  rw cos_mul_cos,
  have : cos((43*pi/180) + (77*pi/180)) = cos (2*pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((43*pi/180) - (77*pi/180)) = cos (-17*pi/90),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
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
  have : cos(-17*pi/90)  =  cos(17*pi/90),
  {
  rw cos_eq_cos_neg_add_int_mul_two_pi (-17*pi/90) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(31*pi/45)  =  cos(17*pi/90),
  {
  rw sin_eq_cos_add_pi_div_two_add_int_mul_two_pi_add_pi (31*pi/45) (-1),
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
  rw cos_pi_div_three,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_1_59_IJYR : sin(pi/3)**2 - 4*cos(pi/3) + 2*cos(2*pi/3)=-9/4:=
begin
  have : cos(2*pi/3)  =  -cos(pi/3),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  norm_num,
end

lemma Trigo_1_60_UGOJ : sin(5*pi/12)*cos(5*pi/12)=1/4:=
begin
  have : sin(5*pi/12)*cos(5*pi/12)  =  sin(5*pi/6)/2,
  {
  have : sin(5*pi/6) = 2*sin(5*pi/12)*cos(5*pi/12),
  {
  have : sin (5*pi/6) = sin(2*(5*pi/12)),
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
  have : sin(5*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
end

lemma Trigo_1_61_AKBN : -sin(pi/12)*cos(pi/4) + sin(pi/4)*cos(pi/12)=1/2:=
begin
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

lemma Trigo_1_62_ZDQM : sin(pi/12)*cos(5*pi/12) + sin(5*pi/12)*cos(pi/12)=1:=
begin
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

lemma Trigo_1_63_BYVR : sin(-19*pi/6)=1/2:=
begin
  have : sin(-19*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-19*pi/6) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_six,
end

lemma Trigo_1_64_CZTJ : 2*sin(pi/12)*cos(pi/12)=1/2:=
begin
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
end

lemma Trigo_1_65_RFIG : sin(-pi/3) + cos(5*pi/4) + tan(-pi/3) + tan(4*pi/3)=-(sqrt(2)+sqrt(3))/2:=
begin
  have : tan(-pi/3)  =  -tan(pi/3),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (-pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_three,
  have : sin(-pi/3)  =  -sin(pi/3),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
  have : cos(5*pi/4)  =  -cos(pi/4),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (5*pi/4) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_four,
  have : tan(4*pi/3)  =  tan(pi/3),
  {
  rw tan_eq_tan_add_int_mul_pi (4*pi/3) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw tan_pi_div_three,
  norm_num,
  field_simp,
end

lemma Trigo_1_66_WMAT : -sin(pi/18)*sin(pi/9) + cos(pi/18)*cos(pi/9)=sqrt(3)/2:=
begin
  have : -sin(pi/18)*sin(pi/9)  =  -cos(pi/18)/2 + cos(pi/6)/2,
  {
  have : sin(pi/18)*sin(pi/9) = cos(pi/18)/2 - cos(pi/6)/2,
  {
  rw mul_comm,
  rw sin_mul_sin,
  have : cos((pi/9) + (pi/18)) = cos (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((pi/9) - (pi/18)) = cos (pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  linarith,
  },
  rw this,
  have : cos(pi/18)*cos(pi/9)  =  cos(pi/6)/2 + cos(pi/18)/2,
  {
  rw mul_comm,
  rw cos_mul_cos,
  have : cos((pi/9) + (pi/18)) = cos (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((pi/9) - (pi/18)) = cos (pi/18),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  rw cos_pi_div_six,
  field_simp,
  ring_exp,
end

lemma Trigo_1_67_EXPB : sin(-52*pi/3)=sqrt(3)/2:=
begin
  have : sin(-52*pi/3)  =  sin(pi/3),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (-52*pi/3) (-9),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_three,
end

lemma Trigo_1_68_ZJNH : -sin(13*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(13*pi/180)=1/2:=
begin
  have : -sin(13*pi/180)*cos(43*pi/180)  =  -sin(14*pi/45)/2 + sin(pi/6)/2,
  {
  have : sin(13*pi/180)*cos(43*pi/180) = -sin(pi/6)/2 + sin(14*pi/45)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((43*pi/180) + (13*pi/180)) = sin (14*pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((43*pi/180) - (13*pi/180)) = sin (pi/6),
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
  have : sin(43*pi/180)*cos(13*pi/180)  =  sin(pi/6)/2 + sin(14*pi/45)/2,
  {
  rw sin_mul_cos,
  have : sin((43*pi/180) + (13*pi/180)) = sin (14*pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((43*pi/180) - (13*pi/180)) = sin (pi/6),
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

lemma Trigo_1_69_WIXQ : -sin(pi/12)*sin(5*pi/6) + sin(5*pi/12)*cos(pi/6)=sqrt(2)/2:=
begin
  have : sin(5*pi/6)  =  sin(pi/6),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
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

lemma Trigo_1_70_KZTD : sin(pi/3)=sqrt(3)/2:=
begin
  rw sin_pi_div_three,
end

lemma Trigo_1_71_ORDR : sin(-pi/3)=-sqrt(3)/2:=
begin
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

lemma Trigo_1_72_OIBK : 4*sin(pi/12)*cos(pi/12)=1:=
begin
  have : 4*sin(pi/12)*cos(pi/12)  =  2*sin(pi/6),
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

lemma Trigo_1_73_JTJS : sin(13*pi/180)*sin(43*pi/180) + sin(47*pi/180)*cos(13*pi/180)=sqrt(3)/2:=
begin
  have : sin(13*pi/180)*sin(43*pi/180)  =  -cos(14*pi/45)/2 + cos(pi/6)/2,
  {
  rw mul_comm,
  rw sin_mul_sin,
  have : cos((43*pi/180) + (13*pi/180)) = cos (14*pi/45),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : cos((43*pi/180) - (13*pi/180)) = cos (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(47*pi/180)*cos(13*pi/180)  =  sin(17*pi/90)/2 + sin(pi/3)/2,
  {
  rw sin_mul_cos,
  have : sin((47*pi/180) + (13*pi/180)) = sin (pi/3),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((47*pi/180) - (13*pi/180)) = sin (17*pi/90),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  },
  rw this,
  have : cos(14*pi/45)  =  sin(17*pi/90),
  {
  rw cos_eq_sin_neg_add_pi_div_two_add_int_mul_two_pi (14*pi/45) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_six,
  rw sin_pi_div_three,
  field_simp,
  ring_exp,
end

lemma Trigo_1_74_FPZB : sqrt(3)*sin(x) + cos(x)=2*cos(x-pi/3):=
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
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  field_simp,
  ring_exp,
end

lemma Trigo_1_75_QZGG : -sin(x)**2*sin(y)**2 + sin(x)**2 + sin(y)**2 + cos(x)**2*cos(y)**2=1:=
begin
  rw cos_sq',
  rw cos_sq',
  have : (1 - sin(x)**2)*(1 - sin(y)**2)  =  sin(x)**2*sin(y)**2 - sin(x)**2 - sin(y)**2 + 1,
  {
  ring_exp,
  },
  rw this,
  norm_num,
  ring_exp,
end

lemma Trigo_1_76_AHWK : sin(pi/3)**2 + 2*cos(2*pi/3)=-1/4:=
begin
  have : cos(2*pi/3)  =  -cos(pi/3),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  rw sin_pi_div_three,
  norm_num,
end

lemma Trigo_1_77_GUMD : 1 - 2*sin(pi/8)**2=sqrt(2)/2:=
begin
  have : 1 - 2*sin(pi/8)**2  =  cos(pi/4),
  {
  have : cos (pi/4) = cos(2*(pi/8)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul'',
  },
  rw this,
  rw cos_pi_div_four,
end

lemma Trigo_1_78_LOWI : sqrt(3)*sin(pi/12)/2 + cos(pi/12)/2=sqrt(2)/2:=
begin
  have : sqrt(3)*sin(pi/12)/2  =  sin(pi/12)*cos(pi/6),
  {
  field_simp,
  ring_exp,
  },
  rw this,
  have : cos(pi/12)/2  =  sin(pi/6)*cos(pi/12),
  {
  field_simp,
  },
  rw this,
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

lemma Trigo_1_79_CUNC : (-sin(pi/3) + sqrt(3)*cos(pi/3))*sin(2*pi/3)/(2*cos(pi/3)) + 1/2=1/2:=
begin
  rw sin_pi_div_three,
  rw cos_pi_div_three,
  norm_num,
  field_simp,
end

lemma Trigo_1_80_WMMO : cos(-52*pi/3)=-1/2:=
begin
  have : cos(-52*pi/3)  =  -cos(pi/3),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (-52*pi/3) (-9),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw cos_pi_div_three,
  norm_num,
end

lemma Trigo_1_81_RBFL : -sin(pi/12)*sin(pi/4) + cos(pi/12)*cos(pi/4) + tan(11*pi/4)=-1/2:=
begin
  have : tan(11*pi/4)  =  -tan(pi/4),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (11*pi/4) (3),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : -sin(pi/12)*sin(pi/4) + cos(pi/12)*cos(pi/4)  =  cos(pi/3),
  {
  have : cos(pi/3) = cos((pi/4) + (pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_add,
  ring,
  },
  rw this,
  rw tan_pi_div_four,
  rw cos_pi_div_three,
  norm_num,
end

lemma Trigo_1_82_CRYV : -sin(13*pi/180)*cos(43*pi/180) + sin(43*pi/180)*cos(13*pi/180)=1/2:=
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

lemma Trigo_1_83_POFB : sin(-25*pi/3) + cos(25*pi/6)=0:=
begin
  have : sin(-25*pi/3)  =  -sin(25*pi/3),
  {
  rw sin_eq_neg_sin_neg_add_int_mul_two_pi (-25*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : sin(25*pi/3)  =  sin(pi/3),
  {
  rw sin_eq_sin_add_int_mul_two_pi (25*pi/3) (-4),
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
  rw sin_pi_div_three,
  rw cos_pi_div_six,
  norm_num,
end

lemma Trigo_1_84_FSBB : cos(3*x)=4*cos(x)**3-3*cos(x):=
begin
  have : cos(3*x)  =  4*cos(x)**3 - 3*cos(x),
  {
  have : cos (3*x) = cos(3*(x)),
  {
  apply congr_arg,
  ring,
  },
  rw cos_three_mul,
  },
  rw this,
end

lemma Trigo_1_85_FJEH : sin(pi/6)**2/2 + sin(pi)*tan(pi/4) - cos(pi/3)**2 + 4*tan(pi/4)**2=31/8:=
begin
  rw cos_pi_div_three,
  rw sin_pi,
  rw sin_pi_div_six,
  rw tan_pi_div_four,
  norm_num,
end

lemma Trigo_1_86_PKQH : sin(7*pi/90)*cos(4*pi/45) + sin(19*pi/45)*cos(37*pi/90)=1/2:=
begin
  have : sin(7*pi/90)*cos(4*pi/45)  =  -sin(pi/90)/2 + sin(pi/6)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
  have : sin((4*pi/45) + (7*pi/90)) = sin (pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((4*pi/45) - (7*pi/90)) = sin (pi/90),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  ring,
  },
  rw this,
  have : sin(19*pi/45)*cos(37*pi/90)  =  sin(pi/90)/2 + sin(5*pi/6)/2,
  {
  rw sin_mul_cos,
  have : sin((19*pi/45) + (37*pi/90)) = sin (5*pi/6),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  have : sin((19*pi/45) - (37*pi/90)) = sin (pi/90),
  {
  apply congr_arg,
  ring,
  },
  rw this,
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
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_1_87_WXUN : (sin(5*pi/4) + tan(11*pi/6))/cos(-2*pi/3)=(3*sqrt(2)+2*sqrt(3))/3:=
begin
  have : sin(5*pi/4)  =  -sin(pi/4),
  {
  rw sin_eq_neg_sin_add_int_mul_two_pi_add_pi (5*pi/4) (-1),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : tan(11*pi/6)  =  -tan(pi/6),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (11*pi/6) (2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : cos(-2*pi/3)  =  -cos(pi/3),
  {
  rw cos_eq_neg_cos_add_int_mul_two_pi_add_pi (-2*pi/3) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi_div_four,
  rw tan_pi_div_six,
  rw cos_pi_div_three,
  field_simp,
  ring_exp,
end

lemma Trigo_1_88_PLZO : sin(5*pi)*cos(3*pi/2)=0:=
begin
  have : sin(5*pi)  =  sin(pi),
  {
  rw sin_eq_sin_add_int_mul_two_pi (5*pi) (-2),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  rw sin_pi,
  norm_num,
end

lemma Trigo_1_89_VSEE : 2*tan(5*pi/6)/(1 - tan(5*pi/6)**2)=-sqrt(3):=
begin
  have : tan(5*pi/6)  =  -tan(pi/6),
  {
  rw tan_eq_neg_tan_neg_add_int_mul_pi (5*pi/6) (1),
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

lemma Trigo_1_90_GKCK : sin(pi/15)*cos(pi/10) + sin(pi/10)*cos(pi/15)=1/2:=
begin
  have : sin(pi/15)*cos(pi/10)  =  -sin(pi/30)/2 + sin(pi/6)/2,
  {
  rw mul_comm,
  rw cos_mul_sin,
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
  have : sin(pi/10)*cos(pi/15)  =  sin(pi/30)/2 + sin(pi/6)/2,
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
  },
  rw this,
  rw sin_pi_div_six,
  norm_num,
  field_simp,
  ring_exp,
end

lemma Trigo_1_91_PNLW : sin(3*pi/20)*cos(7*pi/20) + sin(7*pi/20)*cos(3*pi/20)=1:=
begin
  have : sin(3*pi/20)*cos(7*pi/20) + sin(7*pi/20)*cos(3*pi/20)  =  sin(pi/2),
  {
  have : sin(pi/2) = sin((3*pi/20) + (7*pi/20)),
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

lemma Trigo_1_92_REXZ : -sin(19*pi/180)*sin(13*pi/90) + sin(71*pi/180)*cos(13*pi/90)=sqrt(2)/2:=
begin
  have : sin(71*pi/180)  =  cos(19*pi/180),
  {
  rw sin_eq_cos_neg_add_pi_div_two_add_int_mul_two_pi (71*pi/180) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : -sin(19*pi/180)*sin(13*pi/90) + cos(19*pi/180)*cos(13*pi/90)  =  cos(pi/4),
  {
  have : cos(pi/4) = cos((13*pi/90) + (19*pi/180)),
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

lemma Trigo_1_93_TSCF : (-sin(pi/12) + cos(pi/12))*(sin(pi/12) + cos(pi/12))=sqrt(3)/2:=
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

lemma Trigo_1_94_OCTT : -sin(pi/12)**2 + cos(pi/12)**2=sqrt(3)/2:=
begin
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

lemma Trigo_1_95_OVAE : -sqrt(3)*sin(25*pi/6)**2 + sin(25*pi/6)*cos(25*pi/6)=0:=
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

lemma Trigo_1_96_YBNQ : -sin(5*pi/12)**4 + cos(5*pi/12)**4=-sqrt(3)/2:=
begin
  have : -sin(5*pi/12)**4 + cos(5*pi/12)**4  =  (-sin(5*pi/12)**2 + cos(5*pi/12)**2)*(cos(5*pi/12)**2 + sin(5*pi/12)**2),
  {
  ring_exp,
  },
  rw this,
  have : cos(5*pi/12)**2 + sin(5*pi/12)**2  =  1,
  {
  rw add_comm,
  rw sin_sq_add_cos_sq,
  },
  rw this,
  have : -sin(5*pi/12)**2 + cos(5*pi/12)**2  =  cos(5*pi/6),
  {
  have : cos (5*pi/6) = cos(2*(5*pi/12)),
  {
  apply congr_arg,
  ring,
  },
  rw this,
  rw cos_two_mul',
  ring,
  },
  rw this,
  have : cos(5*pi/6)  =  -cos(pi/6),
  {
  rw cos_eq_neg_cos_neg_add_int_mul_two_pi_add_pi (5*pi/6) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
  have : -cos(pi/6)  =  -sqrt(3)/2,
  {
  have : cos(pi/6) = sqrt(3)/2,
  {
  rw cos_pi_div_six,
  },
  linarith,
  },
  rw this,
  norm_num,
end

lemma Trigo_1_97_TAKY : 2*sin(pi/2) + 1=3:=
begin
  rw sin_pi_div_two,
  norm_num,
end

lemma Trigo_1_98_NLRE : sin(pi/12)*sin(5*pi/12)=1/4:=
begin
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
  rw cos_pi_div_two,
  rw cos_pi_div_three,
  norm_num,
end

lemma Trigo_1_99_BFEN : 2*sin(11*pi/12)*cos(pi/12)=1/2:=
begin
  have : sin(11*pi/12)  =  sin(pi/12),
  {
  rw sin_eq_sin_neg_add_int_mul_two_pi_add_pi (11*pi/12) (0),
  repeat {apply congr_arg _},
  simp,
  linarith,
  },
  rw this,
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
end

