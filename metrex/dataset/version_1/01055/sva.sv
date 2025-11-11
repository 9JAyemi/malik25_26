// SystemVerilog Assertions for add16 and top_module

// ---------------- add16 SVA ----------------
module add16_sva (
    input  logic [15:0] a,
    input  logic [15:0] b,
    input  logic        cin,
    input  logic [15:0] sum,
    input  logic        cout
);
    logic [16:0] full;
    always_comb begin
        full = {1'b0, a} + {1'b0, b} + cin;
        assert (sum == full[15:0])
          else $error("add16 sum mismatch: a=%0h b=%0h cin=%0b sum=%0h exp=%0h", a, b, cin, sum, full[15:0]);
        assert (cout == full[16])
          else $error("add16 cout mismatch: a=%0h b=%0h cin=%0b cout=%0b exp=%0b", a, b, cin, cout, full[16]);
    end

    // Lightweight functional coverage
    cover (full[16] == 1'b1);                            // carry generated
    cover (full[16] == 1'b0);                            // no carry
    cover (a == 16'h0000 && b == 16'h0000 && cin == 0);  // zero case
    cover (a == 16'hFFFF && b == 16'hFFFF && cin == 1);  // max + carry-in
endmodule

bind add16 add16_sva add16_sva_i(.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));


// ---------------- top_module SVA ----------------
module top_module_sva (
    input  logic        clk,
    input  logic        reset,
    input  logic [15:0] in1,
    input  logic [15:0] in2,
    input  logic        enable_mult,
    input  logic [31:0] out,
    input  logic [15:0] adder1_out,
    input  logic [15:0] adder2_out,
    input  logic        adder1_cout,
    input  logic        adder2_cout
);
    // Guard for $past usage
    bit past_valid;
    initial past_valid = 1'b0;
    always_ff @(posedge clk) past_valid <= 1'b1;

    // Output never unknown at sampling edge
    assert property (@(posedge clk) !$isunknown(out));

    // Reset behavior (sampled one cycle later)
    assert property (@(posedge clk) past_valid && $past(reset) |-> out == 32'd0);

    // enable_mult path (zero-extended AND)
    assert property (@(posedge clk)
        past_valid && !$past(reset) && $past(enable_mult)
        |-> out == {16'd0, ($past(in1) & $past(in2))}
    );

    // adder path (concatenation of adder2 result; implies zero-extended upper bits)
    assert property (@(posedge clk)
        past_valid && !$past(reset) && !$past(enable_mult)
        |-> out == { $past(adder2_out), $past(adder2_cout) }
    );

    // Minimal functional coverage
    cover property (@(posedge clk) past_valid && $past(reset) && out == 32'd0);
    cover property (@(posedge clk) past_valid && !$past(reset) && $past(enable_mult));
    cover property (@(posedge clk) past_valid && !$past(reset) && !$past(enable_mult));
    cover property (@(posedge clk) past_valid && !$past(reset) && !$past(enable_mult) && $past(adder2_cout));
endmodule

bind top_module top_module_sva top_sva_i(
    .clk(clk),
    .reset(reset),
    .in1(in1),
    .in2(in2),
    .enable_mult(enable_mult),
    .out(out),
    .adder1_out(adder1_out),
    .adder2_out(adder2_out),
    .adder1_cout(adder1_cout),
    .adder2_cout(adder2_cout)
);