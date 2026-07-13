module arithmetic_module_sva (
    input logic clk,
    input logic Boo_ba1,
    input logic Boo_ba2,
    input logic b,
    input logic Boo_ba3,
    input logic c,
    input logic [3:0] f4_dotnamed
);

// f4 is the sum of the three sub-module outputs.
    check_total_sum: assert property (
        @(posedge clk) f4_dotnamed == (Boo_ba1 << 1) + (Boo_ba2 + b) + (Boo_ba3 - c)
    );

// SubA output is Boo_ba1 shifted left by one.
    check_suba_output: assert property (
        @(posedge clk) f4_dotnamed[3:2] == Boo_ba1 << 1
    );

// SubB output is Boo_ba2 plus b.
    check_subb_output: assert property (
        @(posedge clk) f4_dotnamed[1:0] == Boo_ba2 + b
    );

// SubC output is Boo_ba3 minus c.
    check_subc_output: assert property (
        @(posedge clk) f4_dotnamed[3:2] == Boo_ba3 - c
    );

// When Boo_ba1 is 0, f4[3:2] must be 0.
    check_suba_zero: assert property (
        @(posedge clk) !Boo_ba1 |-> (f4_dotnamed[3:2] == 2'b00)
    );

// When Boo_ba1 is 1, f4[3:2] must be 2.
    check_suba_one: assert property (
        @(posedge clk) Boo_ba1 |-> (f4_dotnamed[3:2] == 2'b10)
    );

// When Boo_ba2 is 0, f4[1:0] must be b.
    check_subb_zero: assert property (
        @(posedge clk) !Boo_ba2 |-> (f4_dotnamed[1:0] == b)
    );

// When Boo_ba2 is 1, f4[1:0] must be b+1.
    check_subb_one: assert property (
        @(posedge clk) Boo_ba2 |-> (f4_dotnamed[1:0] == b + 2'b01)
    );

// When Boo_ba3 is 0, f4[3:2] must be -c.
    check_subc_zero: assert property (
        @(posedge clk) !Boo_ba3 |-> (f4_dotnamed[3:2] == ~c)
    );

// When Boo_ba3 is 1, f4[3:2] must be 1-c.
    check_subc_one: assert property (
        @(posedge clk) Boo_ba3 |-> (f4_dotnamed[3:2] == ~c + 2'b01)
    );

endmodule
