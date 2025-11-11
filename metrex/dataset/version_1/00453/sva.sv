// SVA for the provided design (concise, high-quality, bind-based)
// Place in a separate file and compile alongside DUT. No clock required.

`ifndef SYNTHESIS

// ---------------- full_adder ----------------
module full_adder_sva (
    input logic a, b, cin,
    input logic cout, sum
);
    // Functional correctness: {cout,sum} must equal a+b+cin
    always_comb begin
        assert ({cout, sum} === (a + b + cin))
            else $error("full_adder mismatch: a=%0b b=%0b cin=%0b -> cout=%0b sum=%0b", a,b,cin,cout,sum);

        // X-propagation: known inputs => known outputs
        if (!$isunknown({a,b,cin}))
            assert (!$isunknown({cout,sum}))
                else $error("full_adder produced X/Z on known inputs");

        // Truth-table coverage for all input combinations
        cover ({a,b,cin} == 3'b000);
        cover ({a,b,cin} == 3'b001);
        cover ({a,b,cin} == 3'b010);
        cover ({a,b,cin} == 3'b011);
        cover ({a,b,cin} == 3'b100);
        cover ({a,b,cin} == 3'b101);
        cover ({a,b,cin} == 3'b110);
        cover ({a,b,cin} == 3'b111);

        // Output value coverage
        cover (sum  == 1'b1);
        cover (cout == 1'b1);
    end
endmodule

bind full_adder full_adder_sva fa_sva (
    .a(a), .b(b), .cin(cin),
    .cout(cout), .sum(sum)
);

// ---------------- bit_reversal (identity in given RTL) ----------------
module bit_reversal_sva (
    input logic [7:0] in,
    input logic [7:0] out
);
    // Given RTL implements identity, assert identity
    always_comb begin
        assert (out === in)
            else $error("bit_reversal mismatch: in=%0h out=%0h", in, out);

        if (!$isunknown(in))
            assert (!$isunknown(out))
                else $error("bit_reversal produced X/Z on known input");

        // Simple pattern and per-bit coverage
        cover (in == 8'h00);
        cover (in == 8'hFF);
        cover (in == 8'hAA);
        cover (in == 8'h55);
        for (int i = 0; i < 8; i++) begin
            cover (in == (8'h1 << i)); // each bit seen high
        end
    end
endmodule

bind bit_reversal bit_reversal_sva br_sva (
    .in(in), .out(out)
);

// ---------------- final_module ----------------
module final_module_sva (
    input  logic        a, b, cin,
    input  logic [7:0]  in,
    input  logic        cout, sum,
    input  logic [7:0]  out
);
    always_comb begin
        // End-to-end adder correctness
        assert ({cout, sum} === (a + b + cin))
            else $error("final_module adder mismatch: a=%0b b=%0b cin=%0b -> cout=%0b sum=%0b", a,b,cin,cout,sum);

        // Output composition: out = in | {8{sum}}
        assert (out === (in | {8{sum}}))
            else $error("final_module out mismatch: in=%0h sum=%0b out=%0h", in, sum, out);

        // Helpful special-case checks (redundant but clear)
        assert ((sum == 1'b0) -> (out === in))
            else $error("final_module: sum=0 but out!=in");
        assert ((sum == 1'b1) -> (out === 8'hFF))
            else $error("final_module: sum=1 but out!=FF");

        // Known-in -> known-out
        if (!$isunknown({a,b,cin,in}))
            assert (!$isunknown({cout,sum,out}))
                else $error("final_module produced X/Z on known inputs");

        // Coverage of both out behaviors and carry
        cover (sum == 1'b0 && out == in);
        cover (sum == 1'b1 && out == 8'hFF);
        cover (cout == 1'b1);
    end
endmodule

bind final_module final_module_sva fm_sva (
    .a(a), .b(b), .cin(cin),
    .in(in),
    .cout(cout), .sum(sum),
    .out(out)
);

// ---------------- top_module (end-to-end) ----------------
module top_module_sva (
    input  logic        a, b, cin,
    input  logic [7:0]  in,
    input  logic        cout, sum,
    input  logic [7:0]  out
);
    always_comb begin
        // End-to-end equivalence (redundant with final_module_sva but ensures top wiring)
        assert ({cout, sum} === (a + b + cin))
            else $error("top_module adder mismatch");
        assert (out === (in | {8{sum}}))
            else $error("top_module out mismatch");

        // Minimal coverage end-to-end
        cover ({a,b,cin} == 3'b000);
        cover ({a,b,cin} == 3'b111);
    end
endmodule

bind top_module top_module_sva top_sva (
    .a(a), .b(b), .cin(cin),
    .in(in),
    .cout(cout), .sum(sum),
    .out(out)
);

`endif