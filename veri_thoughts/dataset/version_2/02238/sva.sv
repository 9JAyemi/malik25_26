module mux4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel,
    input logic out
);
    // Out must equal the selected input for all sel values (full functional check).
    check_mux_functional: assert property (
        @(posedge clk) out == ((sel == 2'b00) ? in0 :
                               (sel == 2'b01) ? in1 :
                               (sel == 2'b10) ? in2 :
                                                in3)
    );

    // When sel==00, out equals in0.
    check_sel00_out_eq_in0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in0)
    );

    // When sel==01, out equals in1.
    check_sel01_out_eq_in1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in1)
    );

    // When sel==10, out equals in2.
    check_sel10_out_eq_in2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in2)
    );

    // When sel==11, out equals in3.
    check_sel11_out_eq_in3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in3)
    );

    // If sel and all inputs are stable, out must be stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(sel) && $stable(in0) && $stable(in1) && $stable(in2) && $stable(in3)) |-> $stable(out)
    );
endmodule