// SVA for iic_multiplexer (clockless, bindable, X-aware)
module iic_multiplexer_sva #(parameter int MUX_WIDTH = 2) (
  input  logic                         upstream_scl_T,
  input  logic                         upstream_scl_I,
  input  logic                         upstream_scl_O,
  input  logic                         upstream_sda_T,
  input  logic                         upstream_sda_I,
  input  logic                         upstream_sda_O,
  input  logic [MUX_WIDTH-1:0]         downstream_scl_T,
  input  logic [MUX_WIDTH-1:0]         downstream_scl_I,
  input  logic [MUX_WIDTH-1:0]         downstream_scl_O,
  input  logic [MUX_WIDTH-1:0]         downstream_sda_T,
  input  logic [MUX_WIDTH-1:0]         downstream_sda_I,
  input  logic [MUX_WIDTH-1:0]         downstream_sda_O
);

  // Functional equivalence (combinational, X-aware)
  // Upstream outputs are AND-reductions of downstream inputs
  assert property (@(*) ##0 (upstream_scl_O === (&downstream_scl_I)));
  assert property (@(*) ##0 (upstream_sda_O === (&downstream_sda_I)));

  // Downstream outputs/tri-state controls replicate upstream inputs/controls
  assert property (@(*) ##0 (downstream_scl_O  === {MUX_WIDTH{upstream_scl_I}}));
  assert property (@(*) ##0 (downstream_sda_O  === {MUX_WIDTH{upstream_sda_I}}));
  assert property (@(*) ##0 (downstream_scl_T  === {MUX_WIDTH{upstream_scl_T}}));
  assert property (@(*) ##0 (downstream_sda_T  === {MUX_WIDTH{upstream_sda_T}}));

  // Coverage: AND-reduction semantics exercised
  cover property (@(*) ##0 ((&downstream_scl_I) && (upstream_scl_O === 1'b1)));
  cover property (@(*) ##0 ((|(~downstream_scl_I)) && (upstream_scl_O === 1'b0)));
  cover property (@(*) ##0 ((~(|~downstream_scl_I)) && $isunknown(downstream_scl_I) && $isunknown(upstream_scl_O)));

  cover property (@(*) ##0 ((&downstream_sda_I) && (upstream_sda_O === 1'b1)));
  cover property (@(*) ##0 ((|(~downstream_sda_I)) && (upstream_sda_O === 1'b0)));
  cover property (@(*) ##0 ((~(|~downstream_sda_I)) && $isunknown(downstream_sda_I) && $isunknown(upstream_sda_O)));

  // Coverage: replication paths see both 0 and 1 on O/T vectors (SCL and SDA)
  cover property (@(*) ##0 (downstream_scl_O === {MUX_WIDTH{1'b0}}));
  cover property (@(*) ##0 (downstream_scl_O === {MUX_WIDTH{1'b1}}));
  cover property (@(*) ##0 (downstream_sda_O === {MUX_WIDTH{1'b0}}));
  cover property (@(*) ##0 (downstream_sda_O === {MUX_WIDTH{1'b1}}));

  cover property (@(*) ##0 (downstream_scl_T === {MUX_WIDTH{1'b0}}));
  cover property (@(*) ##0 (downstream_scl_T === {MUX_WIDTH{1'b1}}));
  cover property (@(*) ##0 (downstream_sda_T === {MUX_WIDTH{1'b0}}));
  cover property (@(*) ##0 (downstream_sda_T === {MUX_WIDTH{1'b1}}));

endmodule

// Bind into the DUT (no clock/reset needed)
bind iic_multiplexer iic_multiplexer_sva #(.MUX_WIDTH(MUX_WIDTH)) iic_multiplexer_sva_i (.*);