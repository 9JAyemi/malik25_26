module Span12Mux_s5_v_sva (
    input logic        clk,
    input logic [11:0] I,
    input logic        O
);

    // O matches the exact RTL decode of I.
    check_exact_decode: assert property (
        @(posedge clk)
        O == ((I == 12'b000000000001) ||
              (I == 12'b000000000100) ||
              (I == 12'b000000001000) ||
              (I == 12'b000000010000) ||
              (I == 12'b000000100000) ||
              (I == 12'b000001000000) ||
              (I == 12'b000010000000) ||
              (I == 12'b000100000000) ||
              (I == 12'b001000000000) ||
              (I == 12'b010000000000) ||
              (I == 12'b100000000000))
    );

    // O is high only for the listed input patterns.
    check_output_high_only_for_listed_inputs: assert property (
        @(posedge clk)
        O |-> ((I == 12'b000000000001) ||
               (I == 12'b000000000100) ||
               (I == 12'b000000001000) ||
               (I == 12'b000000010000) ||
               (I == 12'b000000100000) ||
               (I == 12'b000001000000) ||
               (I == 12'b000010000000) ||
               (I == 12'b000100000000) ||
               (I == 12'b001000000000) ||
               (I == 12'b010000000000) ||
               (I == 12'b100000000000))
    );

    // O is low for all other input patterns.
    check_output_low_for_other_inputs: assert property (
        @(posedge clk)
        !((I == 12'b000000000001) ||
          (I == 12'b000000000100) ||
          (I == 12'b000000001000) ||
          (I == 12'b000000010000) ||
          (I == 12'b000000100000) ||
          (I == 12'b000001000000) ||
          (I == 12'b000010000000) ||
          (I == 12'b000100000000) ||
          (I == 12'b001000000000) ||
          (I == 12'b010000000000) ||
          (I == 12'b100000000000))
        |-> !O
    );

    // O is high for input 000000000001.
    check_output_high_for_000000000001: assert property (
        @(posedge clk)
        (I == 12'b000000000001) |-> O
    );

    // O is high for input 000000000100.
    check_output_high_for_000000000100: assert property (
        @(posedge clk)
        (I == 12'b000000000100) |-> O
    );

    // O is high for input 000000001000.
    check_output_high_for_000000001000: assert property (
        @(posedge clk)
        (I == 12'b000000001000) |-> O
    );

    // O is high for input 000000010000.
    check_output_high_for_000000010000: assert property (
        @(posedge clk)
        (I == 12'b000000010000) |-> O
    );

    // O is high for input 000000100000.
    check_output_high_for_000000100000: assert property (
        @(posedge clk)
        (I == 12'b000000100000) |-> O
    );

    // O is high for input 000001000000.
    check_output_high_for_000001000000: assert property (
        @(posedge clk)
        (I == 12'b000001000000) |-> O
    );

    // O is high for input 000010000000.
    check_output_high_for_000010000000: assert property (
        @(posedge clk)
        (I == 12'b000010000000) |-> O
    );

    // O is high for input 000100000000.
    check_output_high_for_000100000000: assert property (
        @(posedge clk)
        (I == 12'b000100000000) |-> O
    );

    // O is high for input 001000000000.
    check_output_high_for_001000000000: assert property (
        @(posedge clk)
        (I == 12'b001000000000) |-> O
    );

    // O is high for input 010000000000.
    check_output_high_for_010000000000: assert property (
        @(posedge clk)
        (I == 12'b010000000000) |-> O
    );

    // O is high for input 100000000000.
    check_output_high_for_100000000000: assert property (
        @(posedge clk)
        (I == 12'b100000000000) |-> O
    );

endmodule