// SVA for prior_enc: concise, high-quality checks and coverage
module prior_enc_sva #(parameter int WIDTH = 64)
(
  input  logic [WIDTH-1:0]           data_in,
  input  logic [$clog2(WIDTH)-1:0]   encode_out,
  input  logic                       enable_out
);
  localparam int N = $clog2(WIDTH);

  // Helper: compute MSB index encoding
  function automatic logic [N-1:0] msb_enc (input logic [WIDTH-1:0] v);
    int i;
    logic [N-1:0] r;
    r = '0;
    for (i = WIDTH-1; i >= 0; i--) begin
      if (v[i]) begin
        r = logic [N-1:0]'(i);
        return r;
      end
    end
    return r; // 0 when v == 0
  endfunction

  // X-safety on inputs
  logic has_x_in;
  always @* has_x_in = $isunknown(data_in);

  // Parameter/width sanity
  initial begin
    assert ($bits(encode_out) == $clog2(WIDTH))
      else $error("encode_out width != $clog2(WIDTH)");
  end

  // 1) enable_out equals OR-reduction of data_in
  assert property (@(*) disable iff (has_x_in)
    (enable_out == (|data_in))
  );

  // 2) When no bit set, outputs are known: enable_out=0 and encode_out=0
  assert property (@(*) disable iff (has_x_in)
    ((data_in == '0) |-> ##0 (!enable_out && encode_out == '0))
  );

  // 3) When enabled, encode_out is MSB index and in range
  assert property (@(*) disable iff (has_x_in)
    (enable_out |-> ##0 (encode_out == msb_enc(data_in) && ($unsigned(encode_out) < WIDTH)))
  );

  // 4) With known inputs, outputs must be free of X/Z
  assert property (@(*) disable iff (has_x_in)
    (!$isunknown({encode_out, enable_out}))
  );

  // Minimal yet meaningful functional coverage
  // a) All-zero case
  cover property (@(*) (data_in == '0 && !enable_out && encode_out == '0));

  // b) Lowest bit set only
  cover property (@(*) (data_in == ({{(WIDTH-1){1'b0}},1'b1}) &&
                        enable_out && encode_out == '0));

  // c) Middle bit set only (if WIDTH > 2)
  if (WIDTH > 2) begin
    localparam int MID = WIDTH/2;
    cover property (@(*) (data_in == (logic [WIDTH-1:0]) (1'b1 << MID) &&
                          enable_out && encode_out == logic [N-1:0]'(MID)));
  end

  // d) Highest bit set only
  cover property (@(*) (data_in == (logic [WIDTH-1:0]) (1'b1 << (WIDTH-1)) &&
                        enable_out && encode_out == logic [N-1:0]'(WIDTH-1)));

  // e) Multiple bits set, highest wins
  cover property (@(*) ((data_in[WIDTH-1] && data_in[0]) &&
                        enable_out && encode_out == logic [N-1:0]'(WIDTH-1)));
endmodule

// Bind into DUT
bind prior_enc prior_enc_sva #(.WIDTH(WIDTH))
  prior_enc_sva_i (.data_in(data_in), .encode_out(encode_out), .enable_out(enable_out));