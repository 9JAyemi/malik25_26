module mux5to1_sva (
    input logic CLK,
    input logic RESETn,
    input logic out,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic [2:0] sel
);
    // When sel==000, out equals in0.
    check_mux_sel_000: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 3'b000) |-> (out == in0)
    );
    // When sel==001, out equals in1.
    check_mux_sel_001: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 3'b001) |-> (out == in1)
    );
    // When sel==010, out equals in2.
    check_mux_sel_010: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 3'b010) |-> (out == in2)
    );
    // When sel==011, out equals in3.
    check_mux_sel_011: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 3'b011) |-> (out == in3)
    );
    // When sel==100, out equals in4.
    check_mux_sel_100: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 3'b100) |-> (out == in4)
    );
    // For sel 101/110/111, out is 0.
    check_mux_invalid_sel_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel inside {3'b101,3'b110,3'b111}) |-> (out == 1'b0)
    );
    // Out equals the RTL conditional chain.
    check_mux_function_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn)
            out == ((sel == 3'b000) ? in0 :
                    (sel == 3'b001) ? in1 :
                    (sel == 3'b010) ? in2 :
                    (sel == 3'b011) ? in3 :
                    (sel == 3'b100) ? in4 :
                    1'b0)
    );
endmodule