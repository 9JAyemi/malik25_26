module digit_select_sva (
    input logic CLK,
    input logic [3:0] d1,
    input logic [3:0] d2,
    input logic [3:0] d3,
    input logic [3:0] d4,
    input logic [1:0] control,
    input logic [3:0] digit
);
    // control 11 selects d1
    check_select_d1_on_11: assert property (
        @(posedge CLK) (control == 2'b11) |-> (digit == d1)
    );

    // control 10 selects d2
    check_select_d2_on_10: assert property (
        @(posedge CLK) (control == 2'b10) |-> (digit == d2)
    );

    // control 01 selects d3
    check_select_d3_on_01: assert property (
        @(posedge CLK) (control == 2'b01) |-> (digit == d3)
    );

    // control 00 selects d4
    check_select_d4_on_00: assert property (
        @(posedge CLK) (control == 2'b00) |-> (digit == d4)
    );

    // Mux function matches RTL ternary expression
    check_mux_function_equivalence: assert property (
        @(posedge CLK) digit == ((control == 2'b11) ? d1 :
                                 (control == 2'b10) ? d2 :
                                 (control == 2'b01) ? d3 : d4)
    );
endmodule