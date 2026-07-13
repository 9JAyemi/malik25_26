module karnaugh_map_sva(
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F
);

    function automatic logic expected_f(
        input logic a,
        input logic b,
        input logic c,
        input logic d,
        input logic e
    );
        begin
            case ({a,b,c,d,e})
                5'b00000: expected_f = 1'b0;
                5'b00001: expected_f = 1'b1;
                5'b00011: expected_f = 1'b0;
                5'b00010: expected_f = 1'b0;
                5'b00110: expected_f = 1'b1;
                5'b00111: expected_f = 1'b0;
                5'b00101: expected_f = 1'b1;
                5'b00100: expected_f = 1'b1;
                5'b01100: expected_f = 1'b1;
                5'b01101: expected_f = 1'b1;
                5'b01111: expected_f = 1'b0;
                5'b01110: expected_f = 1'b1;
                5'b01010: expected_f = 1'b0;
                5'b01011: expected_f = 1'b1;
                5'b01001: expected_f = 1'b0;
                5'b01000: expected_f = 1'b1;
                5'b11000: expected_f = 1'b1;
                5'b11001: expected_f = 1'b0;
                5'b11011: expected_f = 1'b0;
                5'b11010: expected_f = 1'b1;
                5'b11110: expected_f = 1'b0;
                5'b11111: expected_f = 1'b1;
                5'b11101: expected_f = 1'b0;
                5'b11100: expected_f = 1'b1;
                5'b10100: expected_f = 1'b0;
                5'b10101: expected_f = 1'b1;
                5'b10111: expected_f = 1'b0;
                5'b10110: expected_f = 1'b1;
                5'b10010: expected_f = 1'b0;
                5'b10011: expected_f = 1'b1;
                5'b10001: expected_f = 1'b0;
                5'b10000: expected_f = 1'b1;
                default:  expected_f = 1'b0;
            endcase
        end
    endfunction

    // F must match the implemented case table for every sampled input combination.
    check_truth_table_match: assert property (
        @(posedge clk) F == expected_f(A, B, C, D, E)
    );

    // Unknown inputs must select the default branch and drive F low.
    check_default_on_unknown_inputs: assert property (
        @(posedge clk) $isunknown({A, B, C, D, E}) |-> (F == 1'b0)
    );

    // F is always driven to a known value by the case statement and default.
    check_output_known: assert property (
        @(posedge clk) !$isunknown(F)
    );

endmodule