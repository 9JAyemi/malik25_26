module top_module_sva (
    input logic [3:0] binary_in,
    input logic [3:0] final_out
);

    // No RTL clock or reset; sample combinational behavior on $global_clock.
    // Purely combinational path from binary_in to final_out.

    // final_out must match the full combinational function of binary_in.
    check_final_out_function: assert property (
        @($global_clock)
        final_out === {
            (binary_in[2] ^ binary_in[3]),
            (binary_in[1] ^ binary_in[2]),
            (binary_in[0] ^ binary_in[3]),
            (binary_in[0] ^ binary_in[1])
        }
    );

    // final_out[1:0] must match the lower-bit logic produced after Gray and XOR stages.
    check_final_out_lower_bits: assert property (
        @($global_clock)
        final_out[1:0] === {
            (binary_in[0] ^ binary_in[3]),
            (binary_in[0] ^ binary_in[1])
        }
    );

    // final_out[3:2] must match the upper Gray-code bits.
    check_final_out_upper_bits: assert property (
        @($global_clock)
        final_out[3:2] === {
            (binary_in[2] ^ binary_in[3]),
            (binary_in[1] ^ binary_in[2])
        }
    );

    // final_out[0] is binary_in[0] XOR binary_in[1].
    check_final_out_bit0: assert property (
        @($global_clock)
        final_out[0] === (binary_in[0] ^ binary_in[1])
    );

    // final_out[1] is binary_in[0] XOR binary_in[3].
    check_final_out_bit1: assert property (
        @($global_clock)
        final_out[1] === (binary_in[0] ^ binary_in[3])
    );

    // final_out[2] is binary_in[1] XOR binary_in[2].
    check_final_out_bit2: assert property (
        @($global_clock)
        final_out[2] === (binary_in[1] ^ binary_in[2])
    );

    // final_out[3] is binary_in[2] XOR binary_in[3].
    check_final_out_bit3: assert property (
        @($global_clock)
        final_out[3] === (binary_in[2] ^ binary_in[3])
    );

endmodule