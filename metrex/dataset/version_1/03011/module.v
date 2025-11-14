module encode_8b10b (datain, dispin, dataout, dispout) ;
  input [8:0]   datain ;
  input 	dispin ;  output [9:0]	dataout ;
  output	dispout ;


  wire ai = datain[0] ;
  wire bi = datain[1] ;
  wire ci = datain[2] ;
  wire di = datain[3] ;
  wire ei = datain[4] ;
  wire fi = datain[5] ;
  wire gi = datain[6] ;
  wire hi = datain[7] ;
  wire ki = datain[8] ;

  wire aeqb = (ai & bi) | (!ai & !bi) ;
  wire ceqd = (ci & di) | (!ci & !di) ;
  wire l22 = (ai & bi & !ci & !di) |
	     (ci & di & !ai & !bi) |
	     ( !aeqb & !ceqd) ;
  wire l40 = ai & bi & ci & di ;
  wire l04 = !ai & !bi & !ci & !di ;
  wire l13 = ( !aeqb & !ci & !di) |
	     ( !ceqd & !ai & !bi) ;
  wire l31 = ( !aeqb & ci & di) |
	     ( !ceqd & ai & bi) ;

  wire ao = ai ;
  wire bo = (bi & !l40) | l04 ;
  wire co = l04 | ci | (ei & di & !ci & !bi & !ai) ;
  wire do = di & ! (ai & bi & ci) ;
  wire eo = (ei | l13) & ! (ei & di & !ci & !bi & !ai) ;
  wire io = (l22 & !ei) |
	    (ei & !di & !ci & !(ai&bi)) |  (ei & l40) |
	    (ki & ei & di & ci & !bi & !ai) | (ei & !di & ci & !bi & !ai) ;

  wire pd1s6 = (ei & di & !ci & !bi & !ai) | (!ei & !l22 & !l31) ;
  wire nd1s6 = ki | (ei & !l22 & !l13) | (!ei & !di & ci & bi & ai) ;

  wire ndos6 = pd1s6 ;
  wire pdos6 = ki | (ei & !l22 & !l13) ;


  wire alt7 = fi & gi & hi & (ki | 
			      (dispin ? (!ei & di & l31) : (ei & !di & l13))) ;

   
  wire fo = fi & ! alt7 ;
  wire go = gi | (!fi & !gi & !hi) ;
  wire ho = hi ;
  wire jo = (!hi & (gi ^ fi)) | alt7 ;

  wire nd1s4 = fi & gi ;
  wire pd1s4 = (!fi & !gi) | (ki & ((fi & !gi) | (!fi & gi))) ;

  wire ndos4 = (!fi & !gi) ;
  wire pdos4 = fi & gi & hi ;

  wire illegalk = ki & 
		  (ai | bi | !ci | !di | !ei) & (!fi | !gi | !hi | !ei | !l31) ; wire compls6 = (pd1s6 & !dispin) | (nd1s6 & dispin) ;

  wire disp6 = dispin ^ (ndos6 | pdos6) ;

  wire compls4 = (pd1s4 & !disp6) | (nd1s4 & disp6) ;
  assign dispout = disp6 ^ (ndos4 | pdos4) ;

  assign dataout = {(jo ^ compls4), (ho ^ compls4),
		    (go ^ compls4), (fo ^ compls4),
		    (io ^ compls6), (eo ^ compls6),
		    (do ^ compls6), (co ^ compls6),
		    (bo ^ compls6), (ao ^ compls6)} ;

endmodule
