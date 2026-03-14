module mux21_reg_sva (
    input logic I0,
    input logic I1,
    input logic S,
    input logic clk,
    input logic O
);
    // O updates to S-selected input with 1-cycle latency.
    check_mux_register_latency1: assert property (
        @(posedge clk) 1'b1 |=> (O == $past(S ? I1 : I0))
    );

    // If S=0 at a rising edge, next cycle O equals prior I0.
    check_select0_path: assert property (
        @(posedge clk) (S == 1'b0) |=> (O == $past(I0))
    );

    // If S=1 at a rising edge, next cycle O equals prior I1.
    check_select1_path: assert property (
        @(posedge clk) (S == 1'b1) |=> (O == $past(I1))
    );

    // Next-cycle O must equal either prior I0 or prior I1.
    check_next_is_one_of_inputs: assert property (
        @(posedge clk) 1'b1 |=> ((O == $past(I0)) || (O == $past(I1)))
    );

    // If S and I0 are stable with S=0 across a cycle, O holds its value.
    check_hold_when_S0_I0_stable: assert property (
        @(posedge clk) (S == 1'b0 && $stable(S) && $stable(I0)) |=> (O == $past(O))
    );

    // If S and I1 are stable with S=1 across a cycle, O holds its value.
    check_hold_when_S1_I1_stable: assert property (
        @(posedge clk) (S == 1'b1 && $stable(S) && $stable(I1)) |=> (O == $past(O))
    );

    // When inputs are equal at a rising edge, next-cycle O equals that value.
    check_inputs_equal_path: assert property (
        @(posedge clk) (I0 == I1) |=> (O == $past(I0))
    );
endmodule