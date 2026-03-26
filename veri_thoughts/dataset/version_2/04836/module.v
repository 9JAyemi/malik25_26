module shift_register_combination (
    input CLK,
    input PL1,
    input CLR1,
    input PL2,
    input EN2,
    input [3:0] D1,
    input [3:0] D2,
    output [7:0] Q
);

reg [3:0] reg1;
reg [3:0] reg2;

always @(posedge CLK) begin
    if (CLR1) 
        reg1 <= 4'b0;
    else if (PL1) 
        reg1 <= D1;
    else 
        reg1 <= {reg1[2:0], reg1[3]};
end

always @(negedge CLK) begin
    if (EN2) 
        reg2 <= {reg2[2:0], D2};
end

assign Q = {reg1, reg2};

endmodule