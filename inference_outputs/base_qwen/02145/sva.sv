module mux_2_to_1_sva (
    input logic a,
    input logic b,
    input logic sel,
    output logic out
);
    // The logic is purely combinational, so we will use @(posedge clk) for assertions.

    // The output 'out' should be equal to 'a' when 'sel' is 0.
    mux_2_to_1_a: assert property (
        @(posedge clk) $rose(sel) |-> (out == a)
    ) else $error("mux_2_to_1: Output 'out' should be equal to 'a' when 'sel' is 0.");

    // The output 'out' should be equal to 'b' when 'sel' is 1.
    mux_2_to_1_b: assert property (
        @(posedge clk) $rose(~sel) |-> (out == b)
    ) else $error("mux_2_to_1: Output 'out' should be equal to 'b' when 'sel' is 1.");
endmodule