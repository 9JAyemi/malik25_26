// SVA checker for alt_ctl
// Bind example (provide a clock/reset in TB):
// bind alt_ctl alt_ctl_sva u_alt_ctl_sva(.clk(clk), .rst_n(rst_n), .op(op), .func(func), .aluc(aluc));

module alt_ctl_sva(
  input  logic        clk,
  input  logic        rst_n,
  input  logic [5:0]  op,
  input  logic [5:0]  func,
  input  logic [4:0]  aluc
);
  default clocking cb @(posedge clk); endclocking

  // Golden decode (matches first-match semantics of the given DUT)
  function automatic logic [4:0] exp_aluc(input logic [5:0] op_i, input logic [5:0] func_i);
    logic [4:0] a;
    a = 5'd0;
    if (op_i == 6'b000000) begin
      unique case (func_i)
        6'b100000: a = 5'd0;
        6'b100001: a = 5'd1;
        6'b100010: a = 5'd2;
        6'b100011: a = 5'd3;
        6'b100100: a = 5'd4;
        6'b100101: a = 5'd5;
        6'b100110: a = 5'd6;
        6'b100111: a = 5'd7;
        6'b101010: a = 5'd8;
        6'b101011: a = 5'd9;
        6'b000000: a = 5'd10;
        6'b000100: a = 5'd10;
        6'b000010: a = 5'd11; // first match wins over later duplicate
        6'b000110: a = 5'd11;
        6'b000011: a = 5'd12;
        6'b000111: a = 5'd12;
        6'b000001: a = 5'd13;
        default:   a = 5'd0;
      endcase
    end else begin
      unique case (op_i)
        6'b001000: a = 5'd0;
        6'b001001: a = 5'd1;
        6'b001100: a = 5'd4;
        6'b001101: a = 5'd5; // first of several duplicates
        6'b001010: a = 5'd8;
        6'b001111: a = 5'd14;
        default:   a = 5'd0;
      endcase
    end
    return a;
  endfunction

  // Primary functional equivalence
  assert property (disable iff (!rst_n) aluc == exp_aluc(op, func))
    else $error("aluc mismatch: op=%b func=%b aluc=%0d exp=%0d", op, func, aluc, exp_aluc(op,func));

  // Basic validity/X checks
  assert property (disable iff (!rst_n) !$isunknown({op,func}))
    else $error("Unknown (X/Z) on inputs: op/func");
  assert property (disable iff (!rst_n) !$isunknown(aluc))
    else $error("Unknown (X/Z) on aluc");

  // Range guard (redundant with functional check but useful for debug)
  assert property (disable iff (!rst_n) aluc inside {[5'd0:5'd14]})
    else $error("aluc out of expected range");

  // Non-R types must not depend on func
  assert property (disable iff (!rst_n)
                   (op != 6'b000000 && $stable(op) && !$stable(func)) |-> $stable(aluc))
    else $error("aluc illegally depends on func for non-R op");

  // Functional coverage (hit each decoded mapping and defaults)

  // R-type (op==0) mappings
  cover property (op==6'b000000 && func==6'b100000 && aluc==5'd0);
  cover property (op==6'b000000 && func==6'b100001 && aluc==5'd1);
  cover property (op==6'b000000 && func==6'b100010 && aluc==5'd2);
  cover property (op==6'b000000 && func==6'b100011 && aluc==5'd3);
  cover property (op==6'b000000 && func==6'b100100 && aluc==5'd4);
  cover property (op==6'b000000 && func==6'b100101 && aluc==5'd5);
  cover property (op==6'b000000 && func==6'b100110 && aluc==5'd6);
  cover property (op==6'b000000 && func==6'b100111 && aluc==5'd7);
  cover property (op==6'b000000 && func==6'b101010 && aluc==5'd8);
  cover property (op==6'b000000 && func==6'b101011 && aluc==5'd9);
  cover property (op==6'b000000 && func==6'b000000 && aluc==5'd10);
  cover property (op==6'b000000 && func==6'b000100 && aluc==5'd10);
  cover property (op==6'b000000 && func==6'b000010 && aluc==5'd11);
  cover property (op==6'b000000 && func==6'b000110 && aluc==5'd11);
  cover property (op==6'b000000 && func==6'b000011 && aluc==5'd12);
  cover property (op==6'b000000 && func==6'b000111 && aluc==5'd12);
  cover property (op==6'b000000 && func==6'b000001 && aluc==5'd13);
  // R-type default path (unlisted func -> 0)
  cover property (op==6'b000000 &&
                  !(func inside {
                      6'b100000,6'b100001,6'b100010,6'b100011,6'b100100,6'b100101,6'b100110,6'b100111,
                      6'b101010,6'b101011,6'b000000,6'b000100,6'b000010,6'b000110,6'b000011,6'b000111,6'b000001
                   }) && aluc==5'd0);

  // Non-R mappings
  cover property (op==6'b001000 && aluc==5'd0);
  cover property (op==6'b001001 && aluc==5'd1);
  cover property (op==6'b001100 && aluc==5'd4);
  cover property (op==6'b001101 && aluc==5'd5);
  cover property (op==6'b001010 && aluc==5'd8);
  cover property (op==6'b001111 && aluc==5'd14);
  // Non-R default path (unlisted op -> 0)
  cover property (op!=6'b000000 &&
                  !(op inside {6'b001000,6'b001001,6'b001100,6'b001101,6'b001010,6'b001111}) &&
                  aluc==5'd0);

endmodule