// SVA for arbiter
// Quality-focused, concise checks and coverage
// Bind this checker to the DUT:
// bind arbiter arbiter_sva #(.NUM_PORTS(NUM_PORTS), .SEL_WIDTH(SEL_WIDTH)) sva_i (.*);

module arbiter_sva #(
  parameter int NUM_PORTS = 6,
  parameter int SEL_WIDTH = ((NUM_PORTS > 1) ? $clog2(NUM_PORTS) : 1)
)(
  input  logic                      clk,
  input  logic                      rst,
  input  logic [NUM_PORTS-1:0]      request,
  input  logic [NUM_PORTS-1:0]      grant,
  input  logic [SEL_WIDTH-1:0]      select,
  input  logic                      active,
  input  logic [NUM_PORTS-1:0]      token,
  input  logic                      next,
  input  logic [NUM_PORTS-1:0]      order,
  input  logic [NUM_PORTS-1:0]      token_lookahead [NUM_PORTS-1:0]
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Structural invariants
  assert property ($onehot(token));
  assert property ($onehot0(grant));

  // Registered outputs relations
  assert property (grant == $past(token & request));
  assert property (active == (|grant));

  // select/grant consistency
  genvar gi;
  generate
    for (gi = 0; gi < NUM_PORTS; gi++) begin : SEL_MAP
      // If a particular grant bit is 1, select must encode that index
      assert property (grant[gi] |-> (select == gi[0 +: SEL_WIDTH]));
    end
  endgenerate
  // When idle, both grant and select must be zero
  assert property ((!active) |-> (grant == '0 && select == '0));

  // next vs active (registered)
  assert property (active == ~ $past(next));

  // Token behavior
  // Hold when not advancing
  assert property ((!next) |=> token == $past(token));
  // Hold when advancing but no requests exist
  assert property ((next && (request == '0)) |=> token == $past(token));

  // Advance policy (furthest requesting lookahead wins due to coding order)
  genvar k;
  generate
    for (k = 0; k < NUM_PORTS; k++) begin : ADVANCE_CHK
      if (k == NUM_PORTS-1) begin
        assert property ((next && (|order) && order[k]) |=> token == token_lookahead[k]);
      end else begin
        assert property ((next && (|order) && order[k] && ~(|order[NUM_PORTS-1:k+1]))
                         |=> token == token_lookahead[k]);
      end
    end
  endgenerate

  // Reset token to LSB one-hot exactly on reset cycle
  assert property (disable iff (1'b0) (rst |=> token == 'b1));

  // Coverage
  // Each port gets granted sometime
  generate
    for (gi = 0; gi < NUM_PORTS; gi++) begin : COV_GRANT_EACH
      cover property (grant[gi]);
    end
  endgenerate
  // Exercise no-request idle
  cover property (request == '0 && !active);
  // Exercise immediate service (no advance)
  cover property ((!next && (request != '0)) ##1 $stable(token));
  // Exercise advance with multiple requests and token change
  cover property (next && ($countones(request) >= 2) ##1 $changed(token));

endmodule