module d_ff_sc_ena_set (
    output Q,
    input CLK,
    input D,
    input SCD,
    input SCE,
    input SET_B
);

    dfxtp_1 base (
        .q(Q),
        .clk(CLK),
        .d(D),
        .sd(SCD),
        .se(SCE),
        .set(SET_B)
    );

endmodule


module dfxtp_1 (
    output reg q,
    input clk,
    input d,
    input sd,
    input se,
    input set
);

always @(posedge clk or negedge set) begin
    if (!set) begin
        q <= 1'b0; // Asynchronously set the output to 0 (active low SET)
    end
    else if (se) begin
        q <= sd; // Load the scan data when scan enable is high
    end 
    else begin
        q <= d; // Standard D flip-flop behavior
    end
end

endmodule
