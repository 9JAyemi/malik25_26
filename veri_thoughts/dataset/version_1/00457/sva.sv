// SVA checker for alu
module alu_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [7:0]  Aval,
  input  logic [7:0]  Bval,
  input  logic        cin,
  input  logic [1:0]  op,
  input  logic [7:0]  ALUout,
  input  logic        cout
);

  // Reference model (9-bit) matching DUT semantics
  function automatic [8:0] exp9(input logic [7:0] A, B, input logic ci, input logic [1:0] o);
    automatic [8:0] s1;
    begin
      unique case (o)
        2'b00: exp9 = {1'b0, A} + {1'b0, B} + ci;
        2'b10: exp9 = {1'b0, (A & B)};
        2'b01: begin
          s1   = {1'b0, A} + {1'b0, B} + 9'h001;
          exp9 = 9'h100 ^ s1; // flip carry-only, pass sum[7:0]
        end
        2'b11: exp9 = {1'b0, (B > 8'd7 ? 8'h00 : (A << B[2:0]))};
        default: exp9 = 9'h000; // X/Z on op
      endcase
    end
  endfunction

  logic [8:0] exp;
  always_comb exp = exp9(Aval, Bval, cin, op);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional equivalence (covers all op behaviors concisely)
  assert property ({cout, ALUout} == exp)
    else $error("ALU mismatch: op=%b A=%0h B=%0h cin=%0b got={%0b,%0h} exp={%0b,%0h}",
                op, Aval, Bval, cin, cout, ALUout, exp[8], exp[7:0]);

  // Combinational sanity: outputs stable when inputs stable
  assert property ($stable({Aval,Bval,cin,op}) |-> $stable({cout,ALUout}))
    else $error("Outputs changed without input change");

  // Knownness: known inputs imply known outputs
  assert property ((!$isunknown({Aval,Bval,cin,op})) |-> !$isunknown({cout,ALUout}))
    else $error("X/Z on outputs for known inputs");

  // Coverage
  cover property (op == 2'b00);
  cover property (op == 2'b01);
  cover property (op == 2'b10);
  cover property (op == 2'b11);

  // Interesting corners
  cover property (op == 2'b00 && ({1'b0,Aval}+{1'b0,Bval}+cin)[8]);       // add carry-out
  cover property (op == 2'b01 && ({1'b0,Aval}+{1'b0,Bval}+9'h001)[8]);    // inverted-carry path
  cover property (op == 2'b10 && ((Aval & Bval) == 8'h00));               // AND -> zero
  cover property (op == 2'b11 && (Bval == 8'd0));                         // shift by 0
  cover property (op == 2'b11 && (Bval == 8'd7));                         // shift by 7
  cover property (op == 2'b11 && (Bval >  8'd7));                         // overshift -> zero

endmodule

// Example bind (adjust clk/rst paths to your TB)
// bind alu alu_sva u_alu_sva (.* , .clk(tb.clk), .rst_n(tb.rst_n));