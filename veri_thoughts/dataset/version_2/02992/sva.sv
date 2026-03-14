module adder_4bit_carry_sva (
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic       cin,
    input  logic [3:0] sum,
    input  logic       cout,
    input  logic [3:0] temp_sum,
    input  logic       carry1,
    input  logic       carry2,
    input  logic       carry3
);
    // LSB stage: carry1 and temp_sum[0] reflect a[0]+b[0]+cin (2-bit result).
    check_stage0_add: assert property (
        @(posedge a[0] or posedge b[0] or posedge cin or posedge a[1] or posedge b[1] or posedge a[2] or posedge b[2] or posedge a[3] or posedge b[3])
        {carry1, temp_sum[0]} == ({1'b0, a[0]} + {1'b0, b[0]} + cin)
    );

    // Bit1 stage: carry2 and temp_sum[1] reflect a[1]+b[1]+carry1 (2-bit result).
    check_stage1_add: assert property (
        @(posedge a[0] or posedge b[0] or posedge cin or posedge a[1] or posedge b[1] or posedge a[2] or posedge b[2] or posedge a[3] or posedge b[3])
        {carry2, temp_sum[1]} == ({1'b0, a[1]} + {1'b0, b[1]} + carry1)
    );

    // Bit2 stage: carry3 and temp_sum[2] reflect a[2]+b[2]+carry2 (2-bit result).
    check_stage2_add: assert property (
        @(posedge a[0] or posedge b[0] or posedge cin or posedge a[1] or posedge b[1] or posedge a[2] or posedge b[2] or posedge a[3] or posedge b[3])
        {carry3, temp_sum[2]} == ({1'b0, a[2]} + {1'b0, b[2]} + carry2)
    );

    // MSB stage: cout and temp_sum[3] reflect a[3]+b[3]+carry3 (2-bit result).
    check_stage3_add: assert property (
        @(posedge a[0] or posedge b[0] or posedge cin or posedge a[1] or posedge b[1] or posedge a[2] or posedge b[2] or posedge a[3] or posedge b[3])
        {cout, temp_sum[3]} == ({1'b0, a[3]} + {1'b0, b[3]} + carry3)
    );

    // Sum output mirrors temp_sum.
    check_sum_assign: assert property (
        @(posedge a[0] or posedge b[0] or posedge cin or posedge a[1] or posedge b[1] or posedge a[2] or posedge b[2] or posedge a[3] or posedge b[3])
        sum == temp_sum
    );

    // Overall 5-bit result equals a + b + cin.
    check_full_sum: assert property (
        @(posedge a[0] or posedge b[0] or posedge cin or posedge a[1] or posedge b[1] or posedge a[2] or posedge b[2] or posedge a[3] or posedge b[3])
        {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Carry1 is the majority of a[0], b[0], and cin.
    check_carry1_majority: assert property (
        @(posedge a[0] or posedge b[0] or posedge cin or posedge a[1] or posedge b[1] or posedge a[2] or posedge b[2] or posedge a[3] or posedge b[3])
        carry1 == ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))
    );

    // Carry2 is the majority of a[1], b[1], and carry1.
    check_carry2_majority: assert property (
        @(posedge a[0] or posedge b[0] or posedge cin or posedge a[1] or posedge b[1] or posedge a[2] or posedge b[2] or posedge a[3] or posedge b[3])
        carry2 == ((a[1] & b[1]) | (a[1] & carry1) | (b[1] & carry1))
    );

    // Carry3 is the majority of a[2], b[2], and carry2.
    check_carry3_majority: assert property (
        @(posedge a[0] or posedge b[0] or posedge cin or posedge a[1] or posedge b[1] or posedge a[2] or posedge b[2] or posedge a[3] or posedge b[3])
        carry3 == ((a[2] & b[2]) | (a[2] & carry2) | (b[2] & carry2))
    );

    // Cout is the majority of a[3], b[3], and carry3.
    check_cout_majority: assert property (
        @(posedge a[0] or posedge b[0] or posedge cin or posedge a[1] or posedge b[1] or posedge a[2] or posedge b[2] or posedge a[3] or posedge b[3])
        cout == ((a[3] & b[3]) | (a[3] & carry3) | (b[3] & carry3))
    );
endmodule