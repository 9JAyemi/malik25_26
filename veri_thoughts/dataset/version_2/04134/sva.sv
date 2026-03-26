module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] load,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] q
);

    function automatic logic [3:0] adder_model (
        input logic [3:0] A_i,
        input logic [3:0] B_i,
        input logic       Cin_i
    );
        logic [3:0] sum;
        begin
            sum[0] = A_i[0] ^ B_i[0] ^ Cin_i;
            sum[1] = A_i[1] ^ B_i[1] ^ sum[0];
            sum[2] = A_i[2] ^ B_i[2] ^ sum[1];
            sum[3] = A_i[3] ^ B_i[3] ^ sum[2];
            adder_model = sum;
        end
    endfunction

    function automatic logic [3:0] inferred_counter (
        input logic [3:0] A_i,
        input logic [3:0] B_i,
        input logic       Cin_i,
        input logic [3:0] q_i
    );
        begin
            inferred_counter = adder_model(A_i, B_i, Cin_i) - q_i;
        end
    endfunction

    // Reset clears the internal counter by the next cycle.
    reset_clears_counter: assert property (
        @(posedge clk) reset |=> (inferred_counter(A, B, Cin, q) == 4'd0)
    );

    // While reset remains asserted, the inferred counter stays at zero.
    sustained_reset_keeps_counter_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (inferred_counter(A, B, Cin, q) == 4'd0)
    );

    // After reset, q matches the adder output because the counter is zero.
    q_matches_adder_after_reset: assert property (
        @(posedge clk) reset |=> (q == adder_model(A, B, Cin))
    );

    // While reset remains asserted, q continues to match the adder output.
    sustained_reset_keeps_q_on_adder: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (q == adder_model(A, B, Cin))
    );

    // Any nonzero load value is captured into the counter on the next cycle.
    nonzero_load_updates_counter: assert property (
        @(posedge clk) disable iff (reset)
        (load != 4'd0) |=> (inferred_counter(A, B, Cin, q) == $past(load))
    );

    // After a nonzero load, q reflects the current adder output minus the loaded value.
    nonzero_load_updates_q: assert property (
        @(posedge clk) disable iff (reset)
        (load != 4'd0) |=> (q == (adder_model(A, B, Cin) - $past(load)))
    );

    // A zero load value takes the increment path on the next cycle.
    zero_load_increments_counter: assert property (
        @(posedge clk) disable iff (reset)
        (load == 4'd0) |=> (inferred_counter(A, B, Cin, q) == ($past(inferred_counter(A, B, Cin, q)) + 4'd1))
    );

    // After a zero load cycle, q reflects the incremented counter value.
    zero_load_updates_q: assert property (
        @(posedge clk) disable iff (reset)
        (load == 4'd0) |=> (q == (adder_model(A, B, Cin) - ($past(inferred_counter(A, B, Cin, q)) + 4'd1)))
    );

    // The 4-bit counter wraps from 15 back to 0 on increment.
    counter_wraps_from_f_to_0: assert property (
        @(posedge clk) disable iff (reset)
        (load == 4'd0 && (inferred_counter(A, B, Cin, q) == 4'hF))
        |=> (inferred_counter(A, B, Cin, q) == 4'd0)
    );

endmodule