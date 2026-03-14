module gray_code_conversion_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [1:0] gray
);
    // gray[0] must equal binary[0] XOR binary[1].
    check_gray0_is_b0_xor_b1: assert property (
        @(posedge clk) gray[0] == (binary[0] ^ binary[1])
    );

    // gray[1] must equal binary[1] XOR binary[2].
    check_gray1_is_b1_xor_b2: assert property (
        @(posedge clk) gray[1] == (binary[1] ^ binary[2])
    );

    // Vector equivalence for gray encoding.
    check_gray_vector_equiv: assert property (
        @(posedge clk) gray == {binary[1] ^ binary[2], binary[0] ^ binary[1]}
    );

    // Changing binary[3] alone must not affect gray.
    check_gray_independent_of_b3: assert property (
        @(posedge clk) ($changed(binary[3]) && $stable(binary[2:0])) |-> $stable(gray)
    );

    // If only binary[0] changes, gray[0] toggles and gray[1] stays stable.
    check_b0_only_changes_g0: assert property (
        @(posedge clk) ($changed(binary[0]) && $stable(binary[3:1])) |-> ($changed(gray[0]) && $stable(gray[1]))
    );

    // If only binary[1] changes, both gray[0] and gray[1] toggle.
    check_b1_only_changes_both: assert property (
        @(posedge clk) ($changed(binary[1]) && $stable({binary[3:2], binary[0]})) |-> ($changed(gray[0]) && $changed(gray[1]))
    );

    // If only binary[2] changes, gray[1] toggles and gray[0] stays stable.
    check_b2_only_changes_g1: assert property (
        @(posedge clk) ($changed(binary[2]) && $stable({binary[3], binary[1:0]})) |-> ($changed(gray[1]) && $stable(gray[0]))
    );

    // If binary[0] and binary[1] change (others stable), gray[0] stays and gray[1] toggles.
    check_b0_b1_change_effect: assert property (
        @(posedge clk) ($changed(binary[0]) && $changed(binary[1]) && $stable(binary[3:2])) |-> ($stable(gray[0]) && $changed(gray[1]))
    );

    // Parity relation implied by definitions: gray[0]^gray[1] == binary[0]^binary[2].
    check_parity_relation: assert property (
        @(posedge clk) (gray[0] ^ gray[1]) == (binary[0] ^ binary[2])
    );
endmodule