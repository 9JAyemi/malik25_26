module mux4to1_sva (
    input logic CLK,
    input logic out,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel
);
    // out equals the canonical 4:1 mux function of sel and inputs.
    check_mux_function: assert property (
        @(posedge CLK) out == (sel[1] ? (sel[0] ? in3 : in2) : (sel[0] ? in1 : in0))
    );

    // When sel==00, out must equal in0.
    check_sel00_maps_in0: assert property (
        @(posedge CLK) (sel == 2'b00) |-> (out == in0)
    );

    // When sel==01, out must equal in1.
    check_sel01_maps_in1: assert property (
        @(posedge CLK) (sel == 2'b01) |-> (out == in1)
    );

    // When sel==10, out must equal in2.
    check_sel10_maps_in2: assert property (
        @(posedge CLK) (sel == 2'b10) |-> (out == in2)
    );

    // When sel==11, out must equal in3.
    check_sel11_maps_in3: assert property (
        @(posedge CLK) (sel == 2'b11) |-> (out == in3)
    );

    // MSB of sel selects between lower pair (in0/in1) when 0.
    check_group_select_low: assert property (
        @(posedge CLK) (sel[1] == 1'b0) |-> (out == (sel[0] ? in1 : in0))
    );

    // MSB of sel selects between upper pair (in2/in3) when 1.
    check_group_select_high: assert property (
        @(posedge CLK) (sel[1] == 1'b1) |-> (out == (sel[0] ? in3 : in2))
    );

    // Purely combinational: if all inputs and sel are unchanged, out is unchanged.
    check_memoryless: assert property (
        @(posedge CLK) ({in3,in2,in1,in0,sel} == $past({in3,in2,in1,in0,sel})) |-> (out == $past(out))
    );

    // Isolation: with sel==00 stable, changes on in1/in2/in3 do not affect out.
    check_isolation_sel00: assert property (
        @(posedge CLK)
            ($past(sel) == 2'b00 && sel == 2'b00 && in0 == $past(in0) &&
             ((in1 != $past(in1)) || (in2 != $past(in2)) || (in3 != $past(in3))))
        |-> (out == $past(out))
    );

    // Isolation: with sel==01 stable, changes on in0/in2/in3 do not affect out.
    check_isolation_sel01: assert property (
        @(posedge CLK)
            ($past(sel) == 2'b01 && sel == 2'b01 && in1 == $past(in1) &&
             ((in0 != $past(in0)) || (in2 != $past(in2)) || (in3 != $past(in3))))
        |-> (out == $past(out))
    );

    // Isolation: with sel==10 stable, changes on in0/in1/in3 do not affect out.
    check_isolation_sel10: assert property (
        @(posedge CLK)
            ($past(sel) == 2'b10 && sel == 2'b10 && in2 == $past(in2) &&
             ((in0 != $past(in0)) || (in1 != $past(in1)) || (in3 != $past(in3))))
        |-> (out == $past(out))
    );

    // Isolation: with sel==11 stable, changes on in0/in1/in2 do not affect out.
    check_isolation_sel11: assert property (
        @(posedge CLK)
            ($past(sel) == 2'b11 && sel == 2'b11 && in3 == $past(in3) &&
             ((in0 != $past(in0)) || (in1 != $past(in1)) || (in2 != $past(in2))))
        |-> (out == $past(out))
    );
endmodule