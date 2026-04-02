module d_flip_flop_mux_sva (
    input logic clk,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic sel,
    output logic [7:0] q
);
    // Sequential logic: q_reg is updated on the negative edge of clk
    seq_reg_update: assert property (
        @(negedge clk) disable iff (!clk) q_reg == d_in
    );

    // Combinational logic: q is assigned the value of q_reg
    comb_q_assignment: assert property (
        @(posedge clk) disable iff (!clk) q == q_reg
    );

    // Combinational logic: d_in is assigned based on the value of sel
    comb_d_in_assignment: assert property (
        @(posedge clk) disable iff (!clk) d_in == (sel ? d2 : d1)
    );
endmodule