module alu_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [3:0] operation,
    input logic [7:0] result,
    input logic CF,
    input logic ZF,
    input logic SF
);

    localparam logic [3:0] ALU_OP_ADD  = 4'b0000;
    localparam logic [3:0] ALU_OP_SUB  = 4'b0001;
    localparam logic [3:0] ALU_OP_ADC  = 4'b0010;
    localparam logic [3:0] ALU_OP_SBC  = 4'b0011;

    localparam logic [3:0] ALU_OP_AND  = 4'b0100;
    localparam logic [3:0] ALU_OP_OR   = 4'b0101;
    localparam logic [3:0] ALU_OP_NOT  = 4'b0110;
    localparam logic [3:0] ALU_OP_XOR  = 4'b0111;

    localparam logic [3:0] ALU_OP_SHL  = 4'b1000;
    localparam logic [3:0] ALU_OP_SHR  = 4'b1001;
    localparam logic [3:0] ALU_OP_SAL  = 4'b1010;
    localparam logic [3:0] ALU_OP_SAR  = 4'b1011;

    localparam logic [3:0] ALU_OP_ROL  = 4'b1100;
    localparam logic [3:0] ALU_OP_ROR  = 4'b1101;
    localparam logic [3:0] ALU_OP_RCL  = 4'b1110;
    localparam logic [3:0] ALU_OP_RCR  = 4'b1111;

    function automatic logic [10:0] expected_outputs (
        input logic [7:0] a,
        input logic [7:0] b,
        input logic [3:0] op,
        input logic cf_in
    );
        logic [8:0] t;
        begin
            case (op)
                ALU_OP_ADD : t = a + b;
                ALU_OP_SUB : t = a - b;
                ALU_OP_ADC : t = a + b + {7'b0000000, cf_in};
                ALU_OP_SBC : t = a - b - {7'b0000000, cf_in};
                ALU_OP_AND : t = {1'b0, a & b};
                ALU_OP_OR  : t = {1'b0, a | b};
                ALU_OP_NOT : t = {1'b0, ~b};
                ALU_OP_XOR : t = {1'b0, a ^ b};
                ALU_OP_SHL : t = {a[7], a[6:0], 1'b0};
                ALU_OP_SHR : t = {a[0], 1'b0, a[7:1]};
                ALU_OP_SAL : t = {a[7], a[6:0], 1'b0};
                ALU_OP_SAR : t = {a[0], a[7], a[7:1]};
                ALU_OP_ROL : t = {a[7], a[6:0], a[7]};
                ALU_OP_ROR : t = {a[0], a[0], a[7:1]};
                ALU_OP_RCL : t = {a[7], a[6:0], cf_in};
                ALU_OP_RCR : t = {a[0], cf_in, a[7:1]};
                default    : t = 9'h000;
            endcase

            expected_outputs = {t[8], (t[7:0] == 8'h00), t[7], t[7:0]};
        end
    endfunction

    // ZF tracks whether the registered result is zero.
    check_zero_flag_matches_result: assert property (
        @(posedge clk) 1'b1 |=> (ZF == (result == 8'h00))
    );

    // SF tracks the MSB of the registered result.
    check_sign_flag_matches_result: assert property (
        @(posedge clk) 1'b1 |=> (SF == result[7])
    );

    // ADD updates outputs from A + B.
    check_add_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_ADD) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_ADD, $past(CF)))
    );

    // SUB updates outputs from A - B.
    check_sub_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_SUB) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_SUB, $past(CF)))
    );

    // ADC uses the previous CF as carry-in.
    check_adc_outputs_use_prior_cf: assert property (
        @(posedge clk) (operation == ALU_OP_ADC) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_ADC, $past(CF)))
    );

    // SBC uses the previous CF as borrow-in.
    check_sbc_outputs_use_prior_cf: assert property (
        @(posedge clk) (operation == ALU_OP_SBC) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_SBC, $past(CF)))
    );

    // AND updates outputs from A & B.
    check_and_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_AND) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_AND, $past(CF)))
    );

    // OR updates outputs from A | B.
    check_or_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_OR) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_OR, $past(CF)))
    );

    // NOT updates outputs from ~B.
    check_not_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_NOT) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_NOT, $past(CF)))
    );

    // XOR updates outputs from A ^ B.
    check_xor_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_XOR) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_XOR, $past(CF)))
    );

    // SHL shifts A left and moves A[7] into CF.
    check_shl_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_SHL) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_SHL, $past(CF)))
    );

    // SHR shifts A right and moves A[0] into CF.
    check_shr_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_SHR) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_SHR, $past(CF)))
    );

    // SAL behaves the same as SHL in this RTL.
    check_sal_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_SAL) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_SAL, $past(CF)))
    );

    // SAR shifts right arithmetically and moves A[0] into CF.
    check_sar_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_SAR) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_SAR, $past(CF)))
    );

    // ROL rotates A left and moves A[7] into CF.
    check_rol_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_ROL) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_ROL, $past(CF)))
    );

    // ROR rotates A right and moves A[0] into CF.
    check_ror_outputs: assert property (
        @(posedge clk) (operation == ALU_OP_ROR) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_ROR, $past(CF)))
    );

    // RCL rotates A left through the previous CF.
    check_rcl_outputs_use_prior_cf: assert property (
        @(posedge clk) (operation == ALU_OP_RCL) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_RCL, $past(CF)))
    );

    // RCR rotates A right through the previous CF.
    check_rcr_outputs_use_prior_cf: assert property (
        @(posedge clk) (operation == ALU_OP_RCR) |=> ({CF, ZF, SF, result} == expected_outputs($past(A), $past(B), ALU_OP_RCR, $past(CF)))
    );

endmodule