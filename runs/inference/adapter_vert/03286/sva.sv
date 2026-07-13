property ResetSynceotid; @(posedge clk) (rst) |-> (me_aluresult == 0) && (me_d2 == 0) && (me_td == 0) && (me_WREG == 0) && (me_WMEM == 0) && (me_LW == 0) && (me_instr == 32'b100000) ;endproperty 
 
 property SyncLoadeotid; @(posedge clk) ( !rst ) |-> (me_aluresult == ex_aluresult) && (me_d2 == ex_d2) && (me_td == ex_td) && (me_WREG == ex_WREG) && (me_WMEM == ex_WMEM) && (me_LW == ex_LW) && (me_instr == ex_instr) ;endproperty 
 