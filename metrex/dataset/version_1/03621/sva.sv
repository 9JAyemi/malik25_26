// Bind these assertions to the DUT type
bind wifi wifi_sva #(.n(n), .m(m)) u_wifi_sva (
  .clk(clk), .rst(rst), .start(start),
  .valid(valid), .done(done),
  .in(in), .out(out),
  .input_reg(input_reg),
  .encoded_reg(encoded_reg),
  .encoded_reg2(encoded_reg2),
  .decoded_reg(decoded_reg),
  .valid_reg(valid_reg),
  .done_reg(done_reg)
);

module wifi_sva #(parameter int n=8, m=8) (
  input  logic                 clk, rst, start,
  input  logic                 valid, done, valid_reg, done_reg,
  input  logic [n-1:0]         in, input_reg, decoded_reg,
  input  logic [m-1:0]         out, encoded_reg, encoded_reg2
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Sanity on parameters (design uses fixed bit indices 0..7)
  initial assert (n >= 8 && m >= 8)
    else $error("wifi: n and m must be >= 8 (got n=%0d m=%0d)", n, m);

  // Golden encoder/decoder (bit 0..7 as in DUT)
  function automatic logic [m-1:0] f_enc (input logic [n-1:0] v);
    logic [m-1:0] e;
    e[0] = v[0]^v[1]^v[3]^v[4]^v[6];
    e[1] = v[0]^v[2]^v[3]^v[5]^v[6];
    e[2] = v[1]^v[2]^v[3]^v[7];
    e[3] = v[4]^v[5]^v[6]^v[7];
    e[4] = v[0]^v[1]^v[2]^v[4]^v[5];
    e[5] = v[0]^v[1]^v[3]^v[4]^v[7];
    e[6] = v[1]^v[2]^v[4]^v[5]^v[7];
    e[7] = v[0]^v[2]^v[3]^v[6]^v[7];
    return e;
  endfunction
  function automatic logic [n-1:0] f_dec (input logic [m-1:0] e);
    logic [n-1:0] d;
    d[0] = e[0]^e[1]^e[3]^e[4]^e[6];
    d[1] = e[0]^e[2]^e[3]^e[5]^e[6];
    d[2] = e[1]^e[2]^e[3]^e[7];
    d[3] = e[4]^e[5]^e[6]^e[7];
    d[4] = e[0]^e[1]^e[2]^e[4]^e[5];
    d[5] = e[0]^e[1]^e[3]^e[4]^e[7];
    d[6] = e[1]^e[2]^e[4]^e[5]^e[7];
    d[7] = e[0]^e[2]^e[3]^e[6]^e[7];
    return d;
  endfunction

  // No X/Z on outputs after reset
  assert property (!$isunknown({valid, done, out})));

  // Reset values (checked at any clock while rst=1)
  assert property (rst |-> (input_reg==0 && encoded_reg==0 && valid_reg==0 &&
                            encoded_reg2==0 && decoded_reg==0 && done_reg==0));

  // Port consistency
  assert property (valid == valid_reg);
  assert property (done  == done_reg);
  assert property (out   == encoded_reg);

  // Encoder invariant and output correctness
  assert property (encoded_reg == f_enc(input_reg));
  assert property (out == f_enc(input_reg));

  // Start/valid handshake
  assert property (start |=> valid);
  assert property (valid && !start |=> !valid);

  // Capture path into receiver
  assert property (valid |=> encoded_reg2 == $past(encoded_reg));
  assert property ($changed(encoded_reg2) |-> $past(valid));

  // Done protocol
  assert property (valid |=> !done);
  assert property (done |-> (!valid && (encoded_reg2 != '0)));

  // Decoder correctness vs captured encoded_reg2 (catches decode path bugs)
  assert property (done |-> decoded_reg == f_dec(encoded_reg2));

  // End-to-end round-trip if input is held constant across the transaction
  sequence txn; start ##1 valid ##1 done; endsequence
  assert property (txn |-> ($stable(in)[*3] && decoded_reg == $past(in,2)));

  // Coverage
  cover property (start ##1 valid ##1 done);
  cover property (start [*3] ##1 !start ##1 done);
  cover property (done && decoded_reg == f_dec(encoded_reg2));
endmodule