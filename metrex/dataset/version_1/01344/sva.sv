// SVA checker for bin2sevenseg (bindable, concise, full mapping checks + coverage)
module bin2sevenseg_sva(input logic [3:0] inputbin, input logic [6:0] displayout);

  // Recreate DUT constants
  localparam logic [6:0] bit0 = 7'b0000001;
  localparam logic [6:0] bit1 = 7'b0000010;
  localparam logic [6:0] bit2 = 7'b0000100;
  localparam logic [6:0] bit3 = 7'b0001000;
  localparam logic [6:0] bit4 = 7'b0010000;
  localparam logic [6:0] bit5 = 7'b0100000;
  localparam logic [6:0] bit6 = 7'b1000000;

  localparam logic [6:0] zero  = ~(bit0 | bit1 | bit2 | bit3 | bit4 | bit5);
  localparam logic [6:0] one   = ~(bit1 | bit2);
  localparam logic [6:0] two   = ~(bit0 | bit1 | bit3 | bit4 | bit6);
  localparam logic [6:0] three = ~(bit0 | bit1 | bit2 | bit3 | bit6);
  localparam logic [6:0] four  = ~(bit1 | bit2 | bit5 | bit6);
  localparam logic [6:0] five  = ~(bit0 | bit2 | bit3 | bit5 | bit6);
  localparam logic [6:0] six   = ~(bit0 | bit2 | bit3 | bit4 | bit5 | bit6);
  localparam logic [6:0] seven = ~(bit0 | bit1 | bit2);
  localparam logic [6:0] eight = ~(bit0 | bit1 | bit2 | bit3 | bit4 | bit5 | bit6);
  localparam logic [6:0] nine  = ~(bit0 | bit1 | bit2 | bit5 | bit6);
  localparam logic [6:0] blank = ~(7'd0);

  // Hex literals as in DUT
  localparam logic [6:0] A = 7'b0111111; // 10
  localparam logic [6:0] b = 7'b0001111; // 11
  localparam logic [6:0] C = 7'b0100111; // 12
  localparam logic [6:0] d = 7'b0011110; // 13
  localparam logic [6:0] E = 7'b0100111; // 14 (same as C in DUT)
  localparam logic [6:0] F = 7'b0100011; // 15

  function automatic logic [6:0] exp7(input logic [3:0] b4);
    case (b4)
      4'd0:  exp7 = zero;
      4'd1:  exp7 = one;
      4'd2:  exp7 = two;
      4'd3:  exp7 = three;
      4'd4:  exp7 = four;
      4'd5:  exp7 = five;
      4'd6:  exp7 = six;
      4'd7:  exp7 = seven;
      4'd8:  exp7 = eight;
      4'd9:  exp7 = nine;
      4'd10: exp7 = A;
      4'd11: exp7 = b;
      4'd12: exp7 = C;
      4'd13: exp7 = d;
      4'd14: exp7 = E;
      4'd15: exp7 = F;
      default: exp7 = blank;
    endcase
  endfunction

  logic [6:0] exp;

  // Combinational consistency and legality checks
  always_comb begin
    exp = exp7(inputbin);

    // Exact mapping check (delta-cycle)
    assert (#0) (displayout === exp)
      else $error("bin2sevenseg mismatch: in=%0d exp=%b got=%b", inputbin, exp, displayout);

    // Outputs must be known and within the legal set
    assert (#0) !$isunknown(displayout)
      else $error("displayout has X/Z: %b", displayout);

    assert (#0) (displayout inside {
      zero,one,two,three,four,five,six,seven,eight,nine,A,b,C,d,E,F,blank
    }) else $error("displayout illegal pattern: %b", displayout);

    // Unknown input should force blank
    if ($isunknown(inputbin)) begin
      assert (#0) (displayout == blank)
        else $error("unknown input should map to blank. got %b", displayout);
    end
  end

  // Functional coverage: exercise all inputs, observe outputs
  covergroup cg @(inputbin);
    cp_in : coverpoint inputbin { bins all[] = {[0:15]}; }
    cp_out: coverpoint displayout;
    cr    : cross cp_in, cp_out;
  endgroup
  cg cov = new();

endmodule

// Bind into the DUT
bind bin2sevenseg bin2sevenseg_sva u_bin2sevenseg_sva(.inputbin(inputbin), .displayout(displayout));