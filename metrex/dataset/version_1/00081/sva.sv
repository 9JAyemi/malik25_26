// SVA checker for Adder. Bind this to the DUT.
// Focuses on functional equivalence (sum == a+b), structural correctness of carry/half_sum,
// X-propagation, and concise coverage of key corner cases.

module Adder_sva (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [8:0] sum,
    input  logic [7:0] carry,
    input  logic [7:0] half_sum
);
    // Functional equivalence (golden model) and X checks
    always_comb begin
        assert (sum == ({1'b0, a} + {1'b0, b}))
            else $error("Adder mismatch: a=%0h b=%0h sum=%0h exp=%0h", a, b, sum, ({1'b0,a}+{1'b0,b}));

        if (!$isunknown({a,b}))
            assert (!$isunknown(sum))
                else $error("Adder X-prop: sum has X with known inputs");

        // Structural leaf checks
        assert (carry[0] == 1'b0) else $error("carry[0] must be 0");
        assert (half_sum[0] == (a[0] ^ b[0])) else $error("half_sum[0] mismatch");

        // Sum formation checks
        assert (sum[7:0] == half_sum) else $error("sum[7:0] != half_sum");
        assert (sum[8] == ((a[7] & b[7]) | ((a[7] ^ b[7]) & carry[7])))
            else $error("MSB carry (sum[8]) mismatch");
    end

    // Bitwise structural checks for carry chain and half-sum generation
    genvar i;
    generate
        for (i = 1; i < 8; i++) begin : g_bit
            always_comb begin
                assert (carry[i] ==
                        ((a[i-1] & b[i-1]) | (a[i-1] & carry[i-1]) | (b[i-1] & carry[i-1])))
                    else $error("carry[%0d] mismatch", i);

                assert (half_sum[i] == (a[i] ^ b[i] ^ carry[i-1]))
                    else $error("half_sum[%0d] mismatch", i);
            end
        end
    endgenerate

    // Concise functional coverage of key scenarios
    always_comb begin
        cover (a==8'h00 && b==8'h00); // zero + zero
        cover (a==8'hFF && b==8'h01); // full ripple + overflow
        cover (a==8'h80 && b==8'h80); // MSB carry without lower carries
        cover (a==8'h55 && b==8'hAA); // alternating bits, no net carry accumulation
        cover (a==8'hFF && b==8'hFF); // max + max (worst-case carries)
    end
endmodule

// Bind to DUT (accesses internal carry and half_sum)
bind Adder Adder_sva u_adder_sva (.a(a), .b(b), .sum(sum), .carry(carry), .half_sum(half_sum));