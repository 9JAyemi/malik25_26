property AddSynceotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0000) |-> (SUM) == (I0 ^ I1 ^ CIN) && (COUT) == ( (I0 & I1) | (CIN & (I0 ^ I1)) ); endproperty 
 
 property SubSynceotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0001) |-> (SUM) == (I0 ^ I1 ^ CIN) && (COUT) == ( (~I0 & I1) | (CIN & (~I0 ^ I1)) ); endproperty 
 
 property AddSubeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0010) && (  (I3)  ) |-> (SUM) == (I0 ^ I1 ^ CIN) && (COUT) == ( (I0 & I1) | (CIN & (I0 ^ I1)) ); endproperty 
 
 property Subeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0010) &&  ( !(  (I3)  )  ) |-> (SUM) == (I0 ^ I1 ^ CIN) && (COUT) == ( (~I0 & I1) | (CIN & (~I0 ^ I1)) ); endproperty 
 
 property ALUeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0011) |-> (SUM) == ( ~(I0 ^ I1) ) && (COUT) == ( 1'b1 ) ; endproperty 
 
 property ALUeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0100) |-> (SUM) == ( ~(I0 ^ I1) ) && (COUT) == ( (~I0 & I1) | (CIN & (~I0 ^ I1)) ); endproperty 
 
 property ALUeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0101) |-> (SUM) == ( ~(I0 ^ I1) ) && (COUT) == ( (I0 & I1) | (CIN & (I0 | I1)) ); endproperty 
 
 property ALUeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0110) |-> (SUM) == ( I0 ) && (COUT) == ( 1'b0 ) ; endproperty 
 
 property ALUeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0111) |-> (SUM) == ( ~I0 ) && (COUT) == ( 1'b1 ) ; endproperty 
 
 property ALUeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b1000) && (  (I3)  ) |-> (SUM) == ( I0 ) && (COUT) == ( 1'b0 ) ; endproperty 
 
 property ALUeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b1000) &&  ( !(  (I3)  )  ) |-> (SUM) == ( ~I0 ) && (COUT) == ( 1'b1 ) ; endproperty 
 
 property ALUeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b1001) |-> (SUM) == ( I0 & I1 ) && (COUT) == ( I0 & I1 ); endproperty 
 
 property ValidOpseotid; (ALU_MODE) != 4'b111x  |-> (SUM) != 1'b0 && (COUT) != 1'b0; endproperty 
 