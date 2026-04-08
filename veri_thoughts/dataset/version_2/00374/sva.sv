module top_module_assertions (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] c,
    input logic [3:0] d,
    input logic [1:0] sel,
    input logic [3:0] out_mux
);

    // The output must match the full 4-to-1 mux selection function.
    check_combined_mux_function: assert property (
        @(posedge clk) out_mux == (sel[1] ? (sel[0] ? d : c) : (sel[0] ? b : a))
    );

    // sel=00 routes input a to the output.
    check_sel_00_routes_a: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out_mux == a)
    );

    // sel=01 routes input b to the output.
    check_sel_01_routes_b: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out_mux == b)
    );

    // sel=10 routes input c to the output.
    check_sel_10_routes_c: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out_mux == c)
    );

    // sel=11 routes input d to the output.
    check_sel_11_routes_d: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out_mux == d)
    );

    // If all inputs and select are stable, the output must remain stable.
    check_inputs_stable_keep_output_stable: assert property (
        @(posedge clk) $stable({a, b, c, d, sel}) |-> $stable(out_mux)
    );

    // With sel held at 00, only changes on a can affect the output.
    check_sel_00_a_stable_keeps_output_stable: assert property (
        @(posedge clk) (sel == 2'b00 && $past(sel) == 2'b00 && $stable(a)) |-> $stable(out_mux)
    );

    // With sel held at 01, only changes on b can affect the output.
    check_sel_01_b_stable_keeps_output_stable: assert property (
        @(posedge clk) (sel == 2'b01 && $past(sel) == 2'b01 && $stable(b)) |-> $stable(out_mux)
    );

    // With sel held at 10, only changes on c can affect the output.
    check_sel_10_c_stable_keeps_output_stable: assert property (
        @(posedge clk) (sel == 2'b10 && $past(sel) == 2'b10 && $stable(c)) |-> $stable(out_mux)
    );

    // With sel held at 11, only changes on d can affect the output.
    check_sel_11_d_stable_keeps_output_stable: assert property (
        @(posedge clk) (sel == 2'b11 && $past(sel) == 2'b11 && $stable(d)) |-> $stable(out_mux)
    );

endmodule