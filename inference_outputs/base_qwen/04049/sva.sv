module pipereg_w26_sva(
    input logic clk,
    input logic resetn,
    input logic en,
    input logic squashn,
    input logic [25:0] d,
    output logic [25:0] q
);
    // Synchronous reset behavior
    reset_behavior: assert property (
        @(posedge clk) disable iff (!resetn) q == 26'b0
    ) else $error("q should be 0 at reset");

    // Squashn behavior
    squash_behavior: assert property (
        @(posedge clk) disable iff (!resetn) squashn |-> q == 26'b0
    ) else $error("q should be 0 when squashn is asserted");

    // Enable behavior
    enable_behavior: assert property (
        @(posedge clk) disable iff (!resetn) en |-> q == d
    ) else $error("q should be equal to d when enable is asserted");

    // Combinational logic behavior (always block)
    combinational_behavior: assert property (
        @(posedge clk) disable iff (!resetn) (q == (resetn && squashn) ? 26'b0 : (en ? d : q))
    ) else $error("q should be 0 when resetn or squashn is asserted, otherwise it should be equal to d when enable is asserted");

endmodule