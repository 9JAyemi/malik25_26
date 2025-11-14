// SVA checker for top_module
// Uses a sampling clock; provide any free-running TB clock.
module top_module_sva (
  input logic        clk,
  input logic [15:0] in,
  input logic [3:0]  sel,
  input logic        EN,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic [2:0]  op,
  input logic [3:0]  out,
  input logic        valid
);
  default clocking cb @(posedge clk); endclocking

  // Expected combinational functions
  logic [3:0] exp_mux, exp_alu, exp_out;
  logic       exp_valid;

  always_comb begin
    unique case (sel)
      4'd0: exp_mux = in[3:0];
      4'd1: exp_mux = in[7:4];
      4'd2: exp_mux = in[11:8];
      4'd3: exp_mux = in[15:12];
      default: exp_mux = 4'h0;
    endcase

    unique case (op)
      3'b000: exp_alu = (A + B) & 4'hF;
      3'b001: exp_alu = (A - B) & 4'hF;
      3'b010: exp_alu = (A & B);
      3'b011: exp_alu = (A | B);
      3'b100: exp_alu = (A ^ B);
      default: exp_alu = 4'h0;
    endcase
  end

  assign exp_valid = (op != 3'b101);
  assign exp_out   = exp_valid ? exp_alu : (EN ? exp_mux : 4'h0);

  // Core functional checks
  a_valid_def: assert property (valid == exp_valid);
  a_out_func:  assert property (out   == exp_out);

  // Sanity: outputs stable if all driving inputs are stable
  a_stable: assert property (
    $stable({in,sel,EN,A,B,op}) |-> $stable({out,valid})
  );

  // No X/Z on outputs when inputs are known
  a_no_x: assert property (
    !$isunknown({in,sel,EN,A,B,op}) |-> !$isunknown({out,valid})
  );

  // Optional independence: valid depends only on op
  a_valid_dep: assert property ( $stable(op) |-> $stable(valid) );

  // Coverage: ALU ops and arbitration
  c_add:     cover property (op==3'b000 && valid && out==exp_alu);
  c_sub:     cover property (op==3'b001 && valid && out==exp_alu);
  c_and:     cover property (op==3'b010 && valid && out==exp_alu);
  c_or:      cover property (op==3'b011 && valid && out==exp_alu);
  c_xor:     cover property (op==3'b100 && valid && out==exp_alu);
  c_op_101:  cover property (op==3'b101 && !valid && out==(EN?exp_mux:4'h0));
  c_op_110:  cover property (op==3'b110 && valid && out==4'h0);
  c_op_111:  cover property (op==3'b111 && valid && out==4'h0);

  // Coverage: MUX selections and priority
  c_mux0: cover property (!valid && EN && sel==4'd0 && out==in[3:0]);
  c_mux1: cover property (!valid && EN && sel==4'd1 && out==in[7:4]);
  c_mux2: cover property (!valid && EN && sel==4'd2 && out==in[11:8]);
  c_mux3: cover property (!valid && EN && sel==4'd3 && out==in[15:12]);
  c_mux_def: cover property (!valid && EN && sel inside {[4:15]} && out==4'h0);

  c_prio_alu_over_mux: cover property (valid && EN && out==exp_alu);
  c_path_mux:          cover property (!valid && EN && out==exp_mux);
  c_path_zero:         cover property (!valid && !EN && out==4'h0);
endmodule

// Example bind (connect clk from TB)
// bind top_module top_module_sva u_top_module_sva (.*,.clk(tb_clk));