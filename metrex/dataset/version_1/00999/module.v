
module mydff (
    input D ,
    input CLK ,
    input R ,
    output Q
);
wire Qbar ;
reg Q ; // Use blocking assignments
always @(posedge CLK or negedge R) begin
    if (!R) 
        Q <= 1'b0 ;
    else 
        Q <= D ;
end
assign Qbar = ~Q ; // Assign Qbar to the complement of Q
endmodule
