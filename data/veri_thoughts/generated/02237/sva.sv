module mux_4to1_sva (
    input logic clk,         // sampling clock for assertions (RTL is combinational; no reset)
    input logic [3:0] I,
    input logic [1:0] S,
    input logic O
);
    // O equals the selected input bit every cycle.
    check_mux_function: assert property (
        @(posedge clk) O == I[S]
    );

    // When S==2'b00, O must equal I[0].
    check_sel00_map: assert property (
        @(posedge clk) (S == 2'b00) |-> (O == I[0])
    );

    // When S==2'b01, O must equal I[1].
    check_sel01_map: assert property (
        @(posedge clk) (S == 2'b01) |-> (O == I[1])
    );

    // When S==2'b10, O must equal I[2].
    check_sel10_map: assert property (
        @(posedge clk) (S == 2'b10) |-> (O == I[2])
    );

    // When S==2'b11, O must equal I[3].
    check_sel11_map: assert property (
        @(posedge clk) (S == 2'b11) |-> (O == I[3])
    );

    // If S and all I bits are stable, O must be stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(S) && $stable(I)) |-> $stable(O)
    );

    // If S is stable and O changes, then the selected input bit must have changed.
    check_output_change_requires_selected_change: assert property (
        @(posedge clk) ($stable(S) && $changed(O)) |-> 
            ((S == 2'b00 && $changed(I[0])) ||
             (S == 2'b01 && $changed(I[1])) ||
             (S == 2'b10 && $changed(I[2])) ||
             (S == 2'b11 && $changed(I[3])))
    );

    // With S==2'b00 stable and I[0] stable, O must be stable (unselected inputs don't affect O).
    check_sel00_stability: assert property (
        @(posedge clk) ($stable(S) && (S == 2'b00) && $stable(I[0])) |-> $stable(O)
    );

    // With S==2'b01 stable and I[1] stable, O must be stable (unselected inputs don't affect O).
    check_sel01_stability: assert property (
        @(posedge clk) ($stable(S) && (S == 2'b01) && $stable(I[1])) |-> $stable(O)
    );

    // With S==2'b10 stable and I[2] stable, O must be stable (unselected inputs don't affect O).
    check_sel10_stability: assert property (
        @(posedge clk) ($stable(S) && (S == 2'b10) && $stable(I[2])) |-> $stable(O)
    );

    // With S==2'b11 stable and I[3] stable, O must be stable (unselected inputs don't affect O).
    check_sel11_stability: assert property (
        @(posedge clk) ($stable(S) && (S == 2'b11) && $stable(I[3])) |-> $stable(O)
    );
endmodule