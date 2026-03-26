module BrzCombine_9_1_8_sva (
    input logic       out_0r,
    input logic       out_0a,
    input logic [8:0] out_0d,
    input logic       LSInp_0r,
    input logic       LSInp_0a,
    input logic       LSInp_0d,
    input logic       MSInp_0r,
    input logic       MSInp_0a,
    input logic [7:0] MSInp_0d
);

    // out_0a is the OR of the two acknowledge inputs.
    check_ack_or_combine: assert property (
        @($global_clock) out_0a == (LSInp_0a | MSInp_0a)
    );

    // LSInp_0r directly mirrors out_0r.
    check_ls_request_mirror: assert property (
        @($global_clock) LSInp_0r == out_0r
    );

    // MSInp_0r directly mirrors out_0r.
    check_ms_request_mirror: assert property (
        @($global_clock) MSInp_0r == out_0r
    );

    // Both request outputs always match each other.
    check_request_outputs_match: assert property (
        @($global_clock) LSInp_0r == MSInp_0r
    );

    // out_0d[0] comes from LSInp_0d.
    check_data_lsb_mapping: assert property (
        @($global_clock) out_0d[0] == LSInp_0d
    );

    // out_0d[8:1] comes from MSInp_0d[7:0].
    check_data_upper_byte_mapping: assert property (
        @($global_clock) out_0d[8:1] == MSInp_0d
    );

    // The full output data bus is the concatenation of MS and LS inputs.
    check_data_full_concatenation: assert property (
        @($global_clock) out_0d == {MSInp_0d, LSInp_0d}
    );

endmodule