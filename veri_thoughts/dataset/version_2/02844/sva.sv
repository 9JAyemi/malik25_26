module mux_4to1_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic out
);
    // When sel==00, out must equal in[0].
    check_sel00_selects_in0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in[0])
    );

    // When sel==01, out must equal in[1].
    check_sel01_selects_in1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in[1])
    );

    // When sel==10, out must equal in[2].
    check_sel10_selects_in2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in[2])
    );

    // When sel==11, out must equal in[3].
    check_sel11_selects_in3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in[3])
    );

    // If inputs and select are stable, output remains stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(in) && $stable(sel)) |-> $stable(out)
    );

    // With sel==00, if in[0] and sel are stable, output is stable.
    check_isolation_sel00: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(in[0]) && $stable(sel)) |-> $stable(out)
    );

    // With sel==01, if in[1] and sel are stable, output is stable.
    check_isolation_sel01: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(in[1]) && $stable(sel)) |-> $stable(out)
    );

    // With sel==10, if in[2] and sel are stable, output is stable.
    check_isolation_sel10: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(in[2]) && $stable(sel)) |-> $stable(out)
    );

    // With sel==11, if in[3] and sel are stable, output is stable.
    check_isolation_sel11: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(in[3]) && $stable(sel)) |-> $stable(out)
    );

    // Output changes only if sel or inputs change.
    check_output_change_has_cause: assert property (
        @(posedge clk) $changed(out) |-> ($changed(sel) || $changed(in))
    );
endmodule