module bin_to_gray_sva (
    input logic CLK,
    input logic [3:0] bin,
    input logic [3:0] gray
);
    // Gray vector matches combinational mapping from bin.
    check_gray_vector_mapping: assert property (
        @(posedge CLK) gray == { bin[3], (bin[3] ^ bin[2]), (bin[2] ^ bin[1]), (bin[1] ^ bin[0]) }
    );

    // MSB maps directly.
    check_gray_bit3_mapping: assert property (
        @(posedge CLK) gray[3] == bin[3]
    );

    // Next bit is XOR of bin[3] and bin[2].
    check_gray_bit2_mapping: assert property (
        @(posedge CLK) gray[2] == (bin[3] ^ bin[2])
    );

    // Next bit is XOR of bin[2] and bin[1].
    check_gray_bit1_mapping: assert property (
        @(posedge CLK) gray[1] == (bin[2] ^ bin[1])
    );

    // LSB is XOR of bin[1] and bin[0].
    check_gray_bit0_mapping: assert property (
        @(posedge CLK) gray[0] == (bin[1] ^ bin[0])
    );

    // If inputs are stable, outputs are stable (pure combinational function).
    check_stable_input_implies_stable_output: assert property (
        @(posedge CLK) $stable(bin) |-> $stable(gray)
    );

    // Only bin[3] changes -> gray[3] and gray[2] change; others stable.
    check_only_bin3_change_propagation: assert property (
        @(posedge CLK)
            ($changed(bin[3]) && $stable(bin[2]) && $stable(bin[1]) && $stable(bin[0]))
        |-> ($changed(gray[3]) && $changed(gray[2]) && $stable(gray[1]) && $stable(gray[0]))
    );

    // Only bin[2] changes -> gray[2] and gray[1] change; others stable.
    check_only_bin2_change_propagation: assert property (
        @(posedge CLK)
            ($changed(bin[2]) && $stable(bin[3]) && $stable(bin[1]) && $stable(bin[0]))
        |-> ($stable(gray[3]) && $changed(gray[2]) && $changed(gray[1]) && $stable(gray[0]))
    );

    // Only bin[1] changes -> gray[1] and gray[0] change; others stable.
    check_only_bin1_change_propagation: assert property (
        @(posedge CLK)
            ($changed(bin[1]) && $stable(bin[3]) && $stable(bin[2]) && $stable(bin[0]))
        |-> ($stable(gray[3]) && $stable(gray[2]) && $changed(gray[1]) && $changed(gray[0]))
    );

    // Only bin[0] changes -> only gray[0] changes.
    check_only_bin0_change_propagation: assert property (
        @(posedge CLK)
            ($changed(bin[0]) && $stable(bin[3]) && $stable(bin[2]) && $stable(bin[1]))
        |-> ($stable(gray[3]) && $stable(gray[2]) && $stable(gray[1]) && $changed(gray[0]))
    );
endmodule