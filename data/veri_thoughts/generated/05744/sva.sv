module denise_spritepriority_sva (
    input logic       clk,
    input logic [5:0] bplcon2,
    input logic [2:1] nplayfield,
    input logic [7:0] nsprite,
    input logic       sprsel
);

    logic [2:0] sprcode;
    logic [3:0] sprgroup;
    logic       pf1front;
    logic       pf2front;

    assign sprgroup[0] = (nsprite[1:0] == 2'd0) ? 1'b0 : 1'b1;
    assign sprgroup[1] = (nsprite[3:2] == 2'd0) ? 1'b0 : 1'b1;
    assign sprgroup[2] = (nsprite[5:4] == 2'd0) ? 1'b0 : 1'b1;
    assign sprgroup[3] = (nsprite[7:6] == 2'd0) ? 1'b0 : 1'b1;

    always @(*) begin
        if (sprgroup[0])
            sprcode = 3'd1;
        else if (sprgroup[1])
            sprcode = 3'd2;
        else if (sprgroup[2])
            sprcode = 3'd3;
        else if (sprgroup[3])
            sprcode = 3'd4;
        else
            sprcode = 3'd7;
    end

    assign pf1front = (sprcode[2:0] > bplcon2[2:0]) ? 1'b1 : 1'b0;
    assign pf2front = (sprcode[2:0] > bplcon2[5:3]) ? 1'b1 : 1'b0;

    // sprsel must match the RTL decision tree.
    check_sprsel_function: assert property (
        @(posedge clk)
        sprsel == ((sprcode != 3'd7) &&
                   !(pf1front && nplayfield[1]) &&
                   !(pf2front && nplayfield[2]))
    );

    // No active sprite group forces sprsel low.
    check_no_active_sprite_clears_sprsel: assert property (
        @(posedge clk)
        (nsprite == 8'h00) |-> (sprsel == 1'b0)
    );

    // Any active sprite is selected when both playfields are absent.
    check_active_sprite_selected_without_playfields: assert property (
        @(posedge clk)
        (nsprite != 8'h00 && !nplayfield[1] && !nplayfield[2]) |-> (sprsel == 1'b1)
    );

    // PF1 blocks the chosen sprite when its priority is in front.
    check_pf1_front_blocks_sprite: assert property (
        @(posedge clk)
        (sprcode != 3'd7 && pf1front && nplayfield[1]) |-> (sprsel == 1'b0)
    );

    // PF2 blocks the chosen sprite when PF1 does not already block it.
    check_pf2_front_blocks_sprite: assert property (
        @(posedge clk)
        (sprcode != 3'd7 && !(pf1front && nplayfield[1]) && pf2front && nplayfield[2]) |-> (sprsel == 1'b0)
    );

    // Group 0 has priority over group 1.
    check_group0_priority_over_group1: assert property (
        @(posedge clk)
        (sprgroup[0] && sprgroup[1] && nplayfield[1] && !nplayfield[2] && (bplcon2[2:0] == 3'd1)) |-> (sprsel == 1'b1)
    );

    // Group 1 has priority over group 2 when group 0 is inactive.
    check_group1_priority_over_group2: assert property (
        @(posedge clk)
        (!sprgroup[0] && sprgroup[1] && sprgroup[2] && nplayfield[1] && !nplayfield[2] && (bplcon2[2:0] == 3'd2)) |-> (sprsel == 1'b1)
    );

    // Group 2 has priority over group 3 when groups 0 and 1 are inactive.
    check_group2_priority_over_group3: assert property (
        @(posedge clk)
        (!sprgroup[0] && !sprgroup[1] && sprgroup[2] && sprgroup[3] && nplayfield[1] && !nplayfield[2] && (bplcon2[2:0] == 3'd3)) |-> (sprsel == 1'b1)
    );

    // A lone group 3 sprite is hidden by PF1 at threshold 3.
    check_group3_hidden_by_pf1_at_threshold3: assert property (
        @(posedge clk)
        (!sprgroup[0] && !sprgroup[1] && !sprgroup[2] && sprgroup[3] &&
         nplayfield[1] && !nplayfield[2] && (bplcon2[2:0] == 3'd3)) |-> (sprsel == 1'b0)
    );

    // A lone group 3 sprite remains visible against PF1 at threshold 4.
    check_group3_visible_against_pf1_at_threshold4: assert property (
        @(posedge clk)
        (!sprgroup[0] && !sprgroup[1] && !sprgroup[2] && sprgroup[3] &&
         nplayfield[1] && !nplayfield[2] && (bplcon2[2:0] == 3'd4)) |-> (sprsel == 1'b1)
    );

    // PF2 hides a lone group 2 sprite when the upper priority field is 2.
    check_group2_hidden_by_pf2_at_threshold2: assert property (
        @(posedge clk)
        (!sprgroup[0] && !sprgroup[1] && sprgroup[2] && !sprgroup[3] &&
         !nplayfield[1] && nplayfield[2] && (bplcon2[5:3] == 3'd2)) |-> (sprsel == 1'b0)
    );

    // PF2 does not hide a lone group 2 sprite when the upper priority field is 3.
    check_group2_visible_against_pf2_at_threshold3: assert property (
        @(posedge clk)
        (!sprgroup[0] && !sprgroup[1] && sprgroup[2] && !sprgroup[3] &&
         !nplayfield[1] && nplayfield[2] && (bplcon2[5:3] == 3'd3)) |-> (sprsel == 1'b1)
    );

endmodule