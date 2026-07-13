module adder_4bit_sva (
    input logic CLK,          // Formal sampling clock (DUT has no clock/reset)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Z
);
    // 5-bit unsigned sum used to mirror DUT temp_sum behavior
    logic [4:0] sum5;
    assign sum5 = {1'b0, A} + {1'b0, B};

    // Z implements saturating add: Z == min(15, A+B)
    check_saturating_function: assert property (
        @(posedge CLK) Z == ((sum5 > 5'd15) ? 4'hF : sum5[3:0])
    );

    // On overflow (sum > 15), Z saturates to 4'hF
    check_saturates_on_overflow: assert property (
        @(posedge CLK) (sum5 > 5'd15) |-> (Z == 4'hF)
    );

    // Without overflow, Z equals lower 4 bits of the sum
    check_passthrough_without_overflow: assert property (
        @(posedge CLK) (sum5 <= 5'd15) |-> (Z == sum5[3:0])
    );

    // Z is always within 0..15
    check_output_range: assert property (
        @(posedge CLK) Z <= 4'hF
    );
endmodule