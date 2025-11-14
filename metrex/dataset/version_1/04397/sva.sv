// SVA checker for calculator. Bind this file to the DUT.
module calculator_chk (
    input  signed [7:0] a,
    input  signed [7:0] b,
    input         [1:0] op,
    input  signed [7:0] result,
    input               overflow
);
    // Helpers
    function automatic bit in_range (int v);
        return (v >= -128 && v <= 127);
    endfunction

    int A, B, sum, diff, prod, quot;
    logic signed [7:0] trunc_sum, trunc_diff, trunc_prod, trunc_quot;

    // Structural sanity
    assert property (@(a or b or op) !$isunknown(op)) else $error("op is X/Z");
    assert property (@(a or b or op) (op inside {2'b00,2'b01,2'b10,2'b11})) else $error("op invalid");

    // Combinational golden model and checks
    always_comb begin
        A = $signed(a); B = $signed(b);
        sum  = A + B;
        diff = A - B;
        prod = A * B;
        quot = (B != 0) ? (A / B) : 'x;

        trunc_sum  = sum[7:0];
        trunc_diff = diff[7:0];
        trunc_prod = prod[7:0];
        trunc_quot = quot[7:0];

        // Wait a delta so DUT combinational settles (result, then overflow)
        #0;
        unique case (op)
            2'b00: begin // add
                assert (result === trunc_sum)      else $error("ADD result mismatch: %0d+%0d => got %0d exp %0d", A,B,result,trunc_sum);
                assert (overflow === !in_range(sum)) else $error("ADD overflow mismatch (sum=%0d)", sum);
            end
            2'b01: begin // sub
                assert (result === trunc_diff)      else $error("SUB result mismatch: %0d-%0d => got %0d exp %0d", A,B,result,trunc_diff);
                assert (overflow === !in_range(diff)) else $error("SUB overflow mismatch (diff=%0d)", diff);
            end
            2'b10: begin // mul
                assert (result === trunc_prod)      else $error("MUL result mismatch: %0d*%0d => got %0d exp %0d", A,B,result,trunc_prod);
                assert (overflow === !in_range(prod)) else $error("MUL overflow mismatch (prod=%0d)", prod);
            end
            2'b11: begin // div
                if (B == 0) begin
                    assert (overflow === 1'b1) else $error("DIV by zero must assert overflow");
                    assert ($isunknown(result)) else $error("DIV by zero: result should be X");
                end else begin
                    assert (result === trunc_quot)      else $error("DIV result mismatch: %0d/%0d => got %0d exp %0d", A,B,result,trunc_quot);
                    assert (overflow === !in_range(quot)) else $error("DIV overflow mismatch (quot=%0d)", quot);
                end
            end
        endcase

        if (!(op==2'b11 && B==0)) begin
            assert (!$isunknown({result,overflow})) else $error("X/Z on outputs");
        end
    end

    // Functional coverage
    cover property (@(a or b or op) op==2'b00);
    cover property (@(a or b or op) op==2'b01);
    cover property (@(a or b or op) op==2'b10);
    cover property (@(a or b or op) op==2'b11);

    cover property (@(a or b or op) (op==2'b00) && !in_range($signed(a)+$signed(b))); // add overflow
    cover property (@(a or b or op) (op==2'b01) && !in_range($signed(a)-$signed(b))); // sub overflow
    cover property (@(a or b or op) (op==2'b10) && !in_range($signed(a)*$signed(b))); // mul overflow
    cover property (@(a or b or op) (op==2'b11) && (b!=0) && !in_range($signed(a)/$signed(b))); // div overflow
    cover property (@(a or b or op) (op==2'b11) && (b==0)); // div-by-zero stimulus

    cover property (@(a or b or op) a== 127);
    cover property (@(a or b or op) a==-128);
    cover property (@(a or b or op) b== 127);
    cover property (@(a or b or op) b==-128);
endmodule

bind calculator calculator_chk calc_sva (.*);