property ResetSynceotid; @(posedge clk) (rst) |-> control_o == 0 && pc_op == 0 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (rst) != 1'b1 &&  (en)  |-> control_o[0] == en_mem && control_o[1] == should_branch && control_o[2] == imm ;endproperty 
 
 property ValidOpeotid; @(posedge clk) (rst) != 1'b1 &&  (en)  &&  (imm)  |-> pc_op == 2'b10 ;endproperty 
 
 property ValidPcOpeotid; @(posedge clk) (rst) != 1'b1 &&  (en)  &&  ( ! (imm)  ) |-> pc_op == 2'b00 ;endproperty 
 