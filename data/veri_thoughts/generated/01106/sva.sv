module autoinst_multitemplate_sva (
    input  logic clk,
    input  logic rst_n,
    input  logic Boo1,
    input  logic Boo2,
    input  logic Boo3,
    input  logic b,
    input  logic c,
    input  logic [3:0] f4_dotnamed
);
    // f4 equals Boo1 + Boo2 + b + (Boo3 & c), zero-extended to 4 bits.
    check_f4_sum: assert property (
        @(posedge clk) disable iff (!rst_n)
            f4_dotnamed == ({3'b000,Boo1} + {3'b000,Boo2} + {3'b000,b} + {3'b000,(Boo3 & c)})
    );

    // f4 is in the numeric range 0..4.
    check_f4_range: assert property (
        @(posedge clk) disable iff (!rst_n)
            (f4_dotnamed <= 4'd4)
    );

    // MSB of f4 is always 0.
    check_f4_msb_zero: assert property (
        @(posedge clk) disable iff (!rst_n)
            (f4_dotnamed[3] == 1'b0)
    );

    // LSB equals XOR parity of contributors.
    check_f4_lsb_parity: assert property (
        @(posedge clk) disable iff (!rst_n)
            f4_dotnamed[0] == (Boo1 ^ Boo2 ^ b ^ (Boo3 & c))
    );

    // When all contributors are 0, f4 is 0.
    check_f4_all_zero: assert property (
        @(posedge clk) disable iff (!rst_n)
            (!Boo1 && !Boo2 && !b && !(Boo3 & c)) |-> (f4_dotnamed == 4'd0)
    );

    // When only Boo2 and b are 1, f4 is 2.
    check_f4_two_ones_boo2_b: assert property (
        @(posedge clk) disable iff (!rst_n)
            (Boo2 && b && !Boo1 && !(Boo3 & c)) |-> (f4_dotnamed == 4'd2)
    );

    // When c is 0, Boo3 contributes 0 to the sum.
    check_gate_by_c_zero: assert property (
        @(posedge clk) disable iff (!rst_n)
            (c == 1'b0) |-> (f4_dotnamed == ({3'b000,Boo1} + {3'b000,Boo2} + {3'b000,b}))
    );

    // When Boo3 is 0, its contribution is 0.
    check_gate_by_boo3_zero: assert property (
        @(posedge clk) disable iff (!rst_n)
            (Boo3 == 1'b0) |-> (f4_dotnamed == ({3'b000,Boo1} + {3'b000,Boo2} + {3'b000,b}))
    );

    // When Boo1,Boo2,b,Boo3,c are all 1, f4 is 4.
    check_all_four_ones: assert property (
        @(posedge clk) disable iff (!rst_n)
            (Boo1 && Boo2 && b && Boo3 && c) |-> (f4_dotnamed == 4'd4)
    );

    // f4[2] is 1 only when all four contributors are 1.
    check_bit2_only_when_all_four: assert property (
        @(posedge clk) disable iff (!rst_n)
            f4_dotnamed[2] |-> (Boo1 && Boo2 && b && Boo3 && c)
    );

    // When only Boo3&c is 1, f4 is 1.
    check_only_boo3c_one: assert property (
        @(posedge clk) disable iff (!rst_n)
            (!Boo1 && !Boo2 && !b && Boo3 && c) |-> (f4_dotnamed == 4'd1)
    );
endmodule