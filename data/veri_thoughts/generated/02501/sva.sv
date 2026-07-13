module adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);
    // sum equals a + b + cin
    check_sum_add_pos_cin: assert property (
        @(posedge cin) sum == (a + b + cin)
    );

    // cout matches majority of a[3], b[3], cin
    check_cout_majority_pos_cin: assert property (
        @(posedge cin) cout == ((a[3] & b[3]) | (a[3] & cin) | (b[3] & cin))
    );

    // sum[0] is XOR of a[0], b[0], cin
    check_sum0_xor_pos_cin: assert property (
        @(posedge cin) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // When cin=0, sum=a+b and cout=a[3]&b[3]
    check_cin0_behavior_negedge: assert property (
        @(negedge cin) (sum == (a + b)) && (cout == (a[3] & b[3]))
    );

    // When cin=1, sum=a+b+1 and cout=a[3]|b[3]
    check_cin1_behavior_posedge: assert property (
        @(posedge cin) (sum == (a + b + 1'b1)) && (cout == (a[3] | b[3]))
    );

    // If both MSBs are 0 then cout is 0
    check_cout_zero_when_msb_zero: assert property (
        @(posedge cin) ((a[3] == 1'b0) && (b[3] == 1'b0)) |-> (cout == 1'b0)
    );

    // If both MSBs are 1 then cout is 1
    check_cout_one_when_msb_one: assert property (
        @(posedge cin) ((a[3] == 1'b1) && (b[3] == 1'b1)) |-> (cout == 1'b1)
    );

    // If MSBs differ, cout equals cin
    check_cout_tracks_cin_when_msb_mismatch: assert property (
        @(posedge cin) (a[3] ^ b[3]) |-> (cout == cin)
    );

    // cout equals ab + (a^b)cin equivalent form
    check_cout_alt_form: assert property (
        @(posedge cin) cout == ((a[3] & b[3]) | ((a[3] ^ b[3]) & cin))
    );

    // With a=0 and b=0, sum=cin and cout=0
    check_zero_inputs_behavior: assert property (
        @(posedge cin) ((a == 4'b0000) && (b == 4'b0000)) |-> ((sum == {3'b000, cin}) && (cout == 1'b0))
    );
endmodule