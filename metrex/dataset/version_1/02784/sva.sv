// SVA bind file for rotate. Concise, high-quality checks and coverage.
// Bind this to the rotate module: bind rotate rotate_sva u_rotate_sva(.*);

module rotate_sva (
  input  logic [15:0] x,
  input  logic [ 4:0] y,
  input  logic [ 1:0] func,
  input  logic        cfi,
  input  logic        word_op,
  input  logic [15:0] out,
  input  logic        cfo,
  input  logic        ofi,
  input  logic        ofo
);

  // Combinational trigger for assertions
  event comb_e;
  always @(x or y or func or cfi or word_op or ofi) -> comb_e;

  // Helpers
  function automatic [15:0] ror16(input [15:0] v, input int unsigned sh);
    int unsigned s = sh % 16;
    return (v >> s) | (v << (16 - s));
  endfunction
  function automatic [15:0] rol16(input [15:0] v, input int unsigned sh);
    int unsigned s = sh % 16;
    return (v << s) | (v >> (16 - s));
  endfunction

  function automatic [7:0] ror8(input [7:0] v, input int unsigned sh);
    int unsigned s = sh % 8;
    return (v >> s) | (v << (8 - s));
  endfunction
  function automatic [7:0] rol8(input [7:0] v, input int unsigned sh);
    int unsigned s = sh % 8;
    return (v << s) | (v >> (8 - s));
  endfunction

  function automatic [16:0] ror17(input [16:0] v, input int unsigned sh);
    int unsigned s = sh % 17;
    return (v >> s) | (v << (17 - s));
  endfunction
  function automatic [16:0] rol17(input [16:0] v, input int unsigned sh);
    int unsigned s = sh % 17;
    return (v << s) | (v >> (17 - s));
  endfunction

  function automatic [8:0] ror9(input [8:0] v, input int unsigned sh);
    int unsigned s = sh % 9;
    return (v >> s) | (v << (9 - s));
  endfunction
  function automatic [8:0] rol9(input [8:0] v, input int unsigned sh);
    int unsigned s = sh % 9;
    return (v << s) | (v >> (9 - s));
  endfunction

  // Reference model (combinational)
  logic [15:0] exp_out;
  logic        exp_cfo, exp_ofo;

  logic unchanged = word_op ? (y == 5'd0) : (y[3:0] == 4'd0);
  logic [15:0] out_word;
  logic [7:0]  out_byte;
  logic        co_word, co_byte;

  always @* begin
    out_word = 16'h0; out_byte = 8'h0; co_word = 1'b0; co_byte = 1'b0;

    if (word_op) begin
      if (!func[1]) begin
        out_word = func[0] ? rol16(x, y[3:0]) : ror16(x, y[3:0]);
        co_word  = func[0] ? out_word[0] : out_word[15];
      end else begin
        logic [16:0] t = {cfi, x};
        logic [16:0] u = func[0] ? rol17(t, y % 17) : ror17(t, y % 17);
        co_word  = u[16];
        out_word = u[15:0];
      end
      exp_out = out_word;
    end else begin
      if (!func[1]) begin
        out_byte = func[0] ? rol8(x[7:0], y[2:0]) : ror8(x[7:0], y[2:0]);
        co_byte  = func[0] ? out_byte[0] : out_byte[7];
      end else begin
        logic [8:0] t = {cfi, x[7:0]};
        logic [8:0] u = func[0] ? rol9(t, y[3:0] % 9) : ror9(t, y[3:0] % 9);
        co_byte  = u[8];
        out_byte = u[7:0];
      end
      exp_out = {x[15:8], out_byte};
    end

    // Carry flag per DUT spec
    if (unchanged)       exp_cfo = cfi;
    else if (func[1])    exp_cfo = word_op ? co_word : co_byte;
    else                 exp_cfo = word_op ? (func[0] ? out_word[0] : out_word[15])
                                           : (func[0] ? out_byte[0] : out_byte[7]);

    // Overflow flag per DUT spec
    if (unchanged) exp_ofo = ofi;
    else if (func[0]) exp_ofo = word_op ? (exp_cfo ^ exp_out[15])
                                        : (exp_cfo ^ exp_out[7]);
    else              exp_ofo = word_op ? (exp_out[15] ^ exp_out[14])
                                        : (exp_out[7]  ^ exp_out[6]);
  end

  // Valid inputs guard
  let inputs_known = !$isunknown({x,y,func,cfi,word_op,ofi});

  // Core functional equivalence assertion (out, cfo, ofo)
  assert property (@(comb_e) inputs_known ##0 (out == exp_out && cfo == exp_cfo && ofo == exp_ofo))
    else $error("rotate: functional mismatch. out/cfo/ofo incorrect");

  // Unchanged case must pass inputs through
  assert property (@(comb_e) inputs_known && unchanged ##0 (out == x && cfo == cfi && ofo == ofi))
    else $error("rotate: unchanged case failed");

  // Byte-op must preserve upper byte
  assert property (@(comb_e) inputs_known && !word_op ##0 (out[15:8] == x[15:8]))
    else $error("rotate: byte-op upper byte modified");

  // No X-propagation on outputs when inputs are known
  assert property (@(comb_e) inputs_known ##0 !$isunknown({out,cfo,ofo}))
    else $error("rotate: X/Z on outputs with known inputs");

  // Minimal, targeted coverage
  cover property (@(comb_e) inputs_known && word_op && (func==2'b00) && (y[3:0]==4'd1));   // ROR16 by 1
  cover property (@(comb_e) inputs_known && word_op && (func==2'b01) && (y[3:0]==4'd15));  // ROL16 by 15
  cover property (@(comb_e) inputs_known && word_op && (func==2'b10) && (y==5'd16));       // RCR16 by 16
  cover property (@(comb_e) inputs_known && word_op && (func==2'b11) && (y==5'd17));       // RCL16 by 17 (unchanged)
  cover property (@(comb_e) inputs_known && !word_op && (func==2'b00) && (y[2:0]==3'd7));  // ROR8 by 7
  cover property (@(comb_e) inputs_known && !word_op && (func==2'b01) && (y[2:0]==3'd1));  // ROL8 by 1
  cover property (@(comb_e) inputs_known && !word_op && (func==2'b10) && (y[3:0]==4'd8));  // RCR8 by 8
  cover property (@(comb_e) inputs_known && !word_op && (func==2'b11) && (y[3:0]==4'd9));  // RCL8 by 9 (unchanged)
  cover property (@(comb_e) inputs_known && unchanged);                                     // unchanged path
  cover property (@(comb_e) inputs_known && !unchanged && func[1] && (cfo != cfi));         // carry changes on through-carry
  cover property (@(comb_e) inputs_known && !unchanged && (ofo == 1'b1));                   // overflow set in any mode

endmodule