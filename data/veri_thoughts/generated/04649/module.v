module D_behavior(
    input D, Clk,
    output reg Qa, Qb, Qc
    );
    
    always @(posedge Clk) begin
        Qa <= D;
        Qb <= Qa;
        Qc <= Qb;
    end
    
endmodule