# The book and the Lean files

Each statement of the book that is proved here, with the Lean declarations that prove it (or, for a statement proved in part, prove its parts). The numbers are those of the book issued with these files; each Lean docstring names the same label. The proof of a homework problem appears here after its due date.

| Book | Label | Lean |
|---|---|---|
| Definition 1.1 | `def-1n-1` | [`PseudoMetric`](Course/Week01.lean#L920-L935), [`PseudoMetric.isBase_balls`](Course/Week01.lean#L987-L989) |
| Example 1.2 | `ex-1n-2` | [`special_mem_closure_generic`](Course/Week01Examples.lean#L145-L156), [`generic_not_mem_closure_special`](Course/Week01Examples.lean#L158-L169), [`sierpinski_not_pseudoMetrizable`](Course/Week01Examples.lean#L171-L202) |
| Proposition 1.5 | `prop-1n-5` | [`IsBase.criterion`](Course/Week01.lean#L336-L349), [`TopSpace.ofBase`](Course/Week01.lean#L353-L401), [`TopSpace.isBase_ofBase`](Course/Week01.lean#L403-L412) |
| Definition 1.6 | `def-1n-6` | [`subspace`](Course/Week01.lean#L473-L509) |
| Example 1.7 | `ex-1n-sphere` | [`S0_discrete`](Course/Week01Examples.lean#L640-L652) |
| Proposition 1.8 | `prop-1n-composite` | [`continuous_id`](Course/Week01.lean#L276-L278), [`Continuous.comp`](Course/Week01.lean#L280-L285) |
| Proposition 1.9 | `prop-1n-7` | [`continuous_of_closed_cover`](Course/Week01.lean#L696-L726), [`continuous_of_open_cover`](Course/Week01.lean#L728-L749) |
| Proposition 1.10 | `prop-1n-8` | [`homeomorph_iff_isOpenMap`](Course/Week01.lean#L795-L819), [`isOpenMap_iff_isClosedMap`](Course/Week01.lean#L821-L836) |
| Example 1.11 | `ex-1n-9` | [`homeoIooReal`](Course/Week01Examples.lean#L691-L734), [`homeoSquareDisc`](Course/Week01Examples.lean#L932-L953) |
| Example 1.12 | `ex-1n-10` | [`id_discrete_real_not_homeomorph`](Course/Week01Examples.lean#L974-L996), [`expIco_not_homeomorph`](Course/Week01Examples.lean#L1215-L1223) |
| Proposition 1.14 | `prop-1-5` | [`Words.dist_eq_zero`](Course/Week01.lean#L1140-L1149), [`Words.dist_ultra`](Course/Week01.lean#L1151-L1175), [`Words.isBase_cylinders`](Course/Week01.lean#L1229-L1243), [`Words.isClosed_cylinder`](Course/Week01.lean#L1245-L1261) |
| Proposition 1.15 | `prop-1-8` | [`PAdic.ball_eq`](Course/Week01.lean#L1374-L1383), [`PAdic.isBase_classes`](Course/Week01.lean#L1388-L1408), [`PAdic.isClosed_class`](Course/Week01.lean#L1410-L1433) |
| Example 1.18 | `ex-1-11` | [`inter_condition_of_nested`](Course/Week01Examples.lean#L330-L347), [`Words.cylinders_inter_condition`](Course/Week01Examples.lean#L381-L391), [`PAdic.classes_inter_condition`](Course/Week01Examples.lean#L441-L445), [`Ico_inter_Ico_mem`](Course/Week01Examples.lean#L452-L456) |
| Definition 1.19 | `def-1-12` | [`IsNbhdBase`](Course/Week01.lean#L436-L440) |
| Proposition 1.20 | `prop-1-13` | [`isOpen_iff_local`](Course/Week01.lean#L442-L467) |
| Proposition 1.21 | `prop-1-15` | [`continuous_subtype_val`](Course/Week01.lean#L534-L537), [`subspace_coarsest`](Course/Week01.lean#L539-L550) |
| Proposition 1.22 | `prop-1-17` | [`isClosed_subspace_iff`](Course/Week01.lean#L552-L563), [`IsBase.subspace`](Course/Week01.lean#L565-L578), [`closure_subspace`](Course/Week01.lean#L580-L602) |
| Example 1.23 | `ex-1-18` | [`interior_Icc_real`](Course/Week01Examples.lean#L536-L559), [`interior_Icc_subspace`](Course/Week01Examples.lean#L561-L600) |
| Proposition 1.24 | `prop-1-19` | [`continuous_iff_subbase`](Course/Week01.lean#L641-L662), [`continuous_iff_base`](Course/Week01.lean#L664-L668) |
| Definition 1.25 | `def-1-27` | [`IsTopologicalProperty`](Course/Week01.lean#L842-L848) |
| Proposition 1.26 | `prop-1-28` | [`isTopologicalProperty_card`](Course/Week01.lean#L887-L897), [`isTopologicalProperty_card_opens`](Course/Week01.lean#L899-L906), [`isTopologicalProperty_card_isolated`](Course/Week01.lean#L908-L916) |
| Theorem 2.5 | `thm:product-top` | [`pi`](Course/Week02.lean#L505-L524), [`isBase_boxes`](Course/Week02.lean#L526-L528), [`continuous_pi_iff`](Course/Week02.lean#L551-L584) |
| Proposition 2.8 | `prop:coproduct-top` | [`sigma`](Course/Week02.lean#L631-L641), [`isOpen_sigma_iff`](Course/Week02.lean#L646-L649), [`continuous_sigma_iff`](Course/Week02.lean#L655-L662) |
| Definition 2.9 | `def:initial-final` | [`TopSpace.coinduced`](Course/Week02.lean#L288-L298), [`coinduced_finest`](Course/Week02.lean#L317-L323) |
| Example 2.10 | `ex:initial-final` | [`continuous_into_subspace`](Course/Week02Glue.lean#L60-L72), [`continuous_val_comp`](Course/Week02Glue.lean#L74-L79) |
| Definition 2.11 | `def:quotient` | [`quotient`](Course/Week02.lean#L341-L349) |
| Proposition 2.12 | `prop:quotient-univ` | [`continuous_quotient_mk`](Course/Week02.lean#L359-L362), [`continuous_quotient_iff`](Course/Week02.lean#L364-L368), [`continuous_quotient_lift`](Course/Week02.lean#L370-L378), [`quotient_lift_unique`](Course/Week02.lean#L382-L390) |
| Definition 2.15 | `def:pullback` | [`fibreProduct_comm`](Course/Week02Glue.lean#L116-L121) |
| Proposition 2.16 | `prop:pullback-top` | [`fibreProduct_universal`](Course/Week02Glue.lean#L140-L162) |
| Theorem 2.18 | `thm:pushout-top` | [`Pushout`](Course/Week02Glue.lean#L209-L213), [`pushout_universal`](Course/Week02Glue.lean#L279-L297) |
| Definition 2.19 | `def:adjunction` | [`AdjunctionSpace`](Course/Week02Glue.lean#L299-L306) |
| Proposition 2.22 | `prop:stereographic` | [`stereographic1`](Course/Week02Glue.lean#L914-L953), [`stereographic2`](Course/Week02Glue.lean#L1001-L1041) |
| Definition 2.24 | `def:cut-point` | [`IsCutPoint`](Course/Week02Glue.lean#L389-L394) |
| Theorem 2.25 | `thm:one-dimensional` | [`real_not_homeomorph_Ico01`](Course/Week02Glue.lean#L822-L830), [`real_not_homeomorph_I`](Course/Week02Glue.lean#L832-L840), [`I_not_homeomorph_Ico01`](Course/Week02Glue.lean#L842-L858) |
| Remark 2.26 | `rem:non-cut-count` | [`isCutPoint_Ico01`](Course/Week02Glue.lean#L779-L796), [`not_isCutPoint_I_end`](Course/Week02Glue.lean#L798-L820), [`not_isCutPoint_S1`](Course/Week06Circle.lean#L384-L386) |
| Proposition 2.27 | `prop:line-not-plane` | [`real_not_homeomorph_plane`](Course/Week02Glue.lean#L717-L725) |
| Definition 2.29 | `def:graph-space` | [`Graph.Space`](Course/Week02Graphs.lean#L80-L85) |
| Example 2.30 | `ex:graphs` | [`circleGraph`](Course/Week02Graphs.lean#L244-L249), [`intervalGraph`](Course/Week02Graphs.lean#L251-L256), [`eightGraph`](Course/Week02Graphs.lean#L258-L262), [`thetaGraph`](Course/Week02Graphs.lean#L264-L268) |
| Example 2.33 | `ex:eight-vs-circle` | [`eight_not_homeomorph_circle`](Course/Week02Graphs.lean#L417-L436) |
| Example 3.17 | `ex-3n-he` | [`Plane0.isDeformationRetract_circ`](Course/Week06Circle.lean#L266-L299), [`Plane0.homotopyEquivalent_S1`](Course/Week06Circle.lean#L326-L328) |
| Theorem 3.30 | `thm-3n-eh` | [`eckmann_hilton`](Course/Week07Covering.lean#L1373-L1412) |
| Definition 4.1 | `def:path-homotopy` | [`PathHomotopy`](Course/Week04.lean#L518-L530) |
| Definition 4.2 | `def:concatenation` | [`Path.refl`](Course/Week04.lean#L461-L462), [`Path.symm`](Course/Week04.lean#L467-L470), [`Path.trans`](Course/Week04.lean#L478-L491) |
| Proposition 4.3 | `prop:associativity` | [`Path.Homotopic.trans_assoc`](Course/Week04.lean#L743-L754) |
| Remark 4.4 | `rem:pushout-paths` | [`Path.trans_assoc_eq`](Course/Week04.lean#L691-L741) |
| Lemma 4.5 | `lem:reparam` | [`Path.reparam_homotopic`](Course/Week04.lean#L662-L687) |
| Theorem 4.6 | `thm:groupoid-laws` | [`Path.Homotopic.hcomp`](Course/Week04.lean#L636-L640), [`Path.Homotopic.trans_assoc`](Course/Week04.lean#L743-L754), [`Path.Homotopic.refl_trans`](Course/Week04.lean#L778-L785), [`Path.Homotopic.trans_symm`](Course/Week04.lean#L793-L829) |
| Corollary 4.7 | `cor:pi1-group` | [`PathClass.comp`](Course/Week04.lean#L855-L861), [`PathClass.inv`](Course/Week04.lean#L863-L866), [`pi1.instGroup`](Course/Week04.lean#L916-L930) |
| Proposition 4.8 | `prop:loops-circle` | [`loopEquiv`](Course/Week04More.lean#L557-L575), [`homotopic_iff_pointedHomotopic`](Course/Week04More.lean#L583-L620), [`pi1EquivPointed`](Course/Week04More.lean#L641-L655) |
| Definition 4.16 | `def:equalizer` | [`equalizer_condition`](Course/Week04More.lean#L71-L80), [`coequalizer_condition`](Course/Week04More.lean#L134-L142) |
| Proposition 4.17 | `prop:equalizer-top` | [`equalizer_universal`](Course/Week04More.lean#L95-L112), [`coequalizer_universal`](Course/Week04More.lean#L162-L177) |
| Theorem 4.18 | `thm:limits-from-products` | [`limit_universal`](Course/Week04More.lean#L249-L274), [`colimit_universal`](Course/Week04More.lean#L308-L340) |
| Corollary 4.19 | `cor:top-complete` | [`limit`](Course/Week04More.lean#L218-L222), [`limit_universal`](Course/Week04More.lean#L249-L274), [`Colimit`](Course/Week04More.lean#L285-L288), [`colimit_universal`](Course/Week04More.lean#L308-L340) |
| Definition 4.28 | `def:quaternions` | [`S3`](Course/Week04More.lean#L1167-L1169) |
| Definition 4.31 | `def:hopf-map` | [`hopf`](Course/Week04More.lean#L1198-L1209) |
| Proposition 4.32 | `prop:hopf-fibres` | [`conj_i_eq`](Course/Week04More.lean#L1187-L1196), [`hopf_eq_iff`](Course/Week04More.lean#L1300-L1313), [`hopf_surjective`](Course/Week04More.lean#L1315-L1358), [`hopfFibreHomeo`](Course/Week04More.lean#L1368-L1407) |
| Definition 4.36 | `def:simplex` | [`simplex`](Course/Week04More.lean#L672-L675), [`simplexBoundary`](Course/Week04More.lean#L677-L679) |
| Proposition 4.38 | `prop:simplex-ball` | [`simplexHomeoD1`](Course/Week04More.lean#L717-L749), [`simplexHomeoD1_boundary`](Course/Week04More.lean#L751-L768), [`D2HomeoSimplex`](Course/Week04More.lean#L1041-L1103), [`D2HomeoSimplex_boundary`](Course/Week04More.lean#L1105-L1139) |
| Exercise 4.E1 | `exr-4-unit` | [`Path.refl_trans_eq`](Course/Week04.lean#L756-L765), [`Path.trans_refl_eq`](Course/Week04.lean#L767-L776) |
| Exercise 4.E10 | `exr-4-hopf` | [`conj_i_eq`](Course/Week04More.lean#L1187-L1196) |
| Proposition 5.2 | `prop:attach-injects` | [`attach_inl_injective`](Course/Week05.lean#L2272-L2277), [`attach_inr_injOn`](Course/Week05.lean#L2279-L2286), [`attach_inl_isClosedMap`](Course/Week05.lean#L2288-L2339), [`attach_inr_isOpen_image`](Course/Week05.lean#L2341-L2379) |
| Definition 5.17 | `def:presentation` | [`Surface.Presentation`](Course/Week05.lean#L159-L162), [`Surface.IsSurface`](Course/Week05.lean#L172-L175) |
| Example 5.19 | `ex:standard-presentations` | [`Surface.sphere`](Course/Week05.lean#L227-L228), [`Surface.torusWord`](Course/Week05.lean#L234-L241), [`Surface.crossWord`](Course/Week05.lean#L246-L250) |
| Definition 5.21 | `def:elementary` | [`Surface.Move`](Course/Week05.lean#L270-L319), [`Surface.Elementary`](Course/Week05.lean#L321-L323) |
| Proposition 5.23 | `prop:connected-sum-words` | [`Surface.connected_sum_words`](Course/Week05.lean#L645-L685) |
| Lemma 5.24 | `lem:twisted-pair` | [`Surface.twisted_pair`](Course/Week05.lean#L443-L561) |
| Lemma 5.25 | `lem:klein` | [`Surface.klein`](Course/Week05.lean#L563-L574) |
| Lemma 5.28 | `lem:torus-rp2` | [`Surface.torus_rp2`](Course/Week05.lean#L576-L643) |
| Theorem 5.30 | `thm:classification-I` | [`Surface.paste_twisted`](Course/Week05Classification.lean#L124-L139), [`Surface.step2_fold`](Course/Week05Classification.lean#L223-L285), [`Surface.handle_form`](Course/Week05Classification.lean#L379-L428), [`Surface.mixedWord_standard`](Course/Week05Classification.lean#L742-L751), [`Surface.step6`](Course/Week05Classification.lean#L1068-L1122) |
| Remark 5.31 | `rem:classification-II-owed` | [`Surface.not_equiv_torus_cross`](Course/Week05Classification.lean#L85-L94) |
| Definition 5.32 | `def:euler-presentation` | [`Surface.chi`](Course/Week05.lean#L853-L860) |
| Proposition 5.33 | `prop:chi-invariant` | [`Surface.chi_move`](Course/Week05.lean#L1893-L1919), [`Surface.chi_equiv`](Course/Week05.lean#L1921-L1929) |
| Proposition 5.34 | `prop:chi-standard` | [`Surface.chi_sphere`](Course/Week05.lean#L1966-L1997), [`Surface.chi_torus`](Course/Week05.lean#L2037-L2106), [`Surface.chi_cross`](Course/Week05.lean#L2143-L2187) |
| Theorem 6.1 | `thm:change-basepoint` | [`beta`](Course/Week06Invariance.lean#L132-L136), [`beta_symm`](Course/Week06Invariance.lean#L142-L145), [`beta_symm_beta`](Course/Week06Invariance.lean#L171-L182) |
| Definition 6.3 | `def:simply-connected` | [`SimplyConnected`](Course/Week06Invariance.lean#L195-L198), [`simplyConnected_iff_exists`](Course/Week06Invariance.lean#L208-L223) |
| Proposition 6.4 | `prop:induced` | [`induced`](Course/Week06Brouwer.lean#L130-L152), [`induced_comp`](Course/Week06Brouwer.lean#L158-L169), [`induced_id`](Course/Week06Brouwer.lean#L171-L177) |
| Lemma 6.5 | `lem:homotopy-basepoint` | [`Homotopy.homotopic_square`](Course/Week06Invariance.lean#L306-L316), [`induced_eq_beta_comp`](Course/Week06Invariance.lean#L340-L345) |
| Theorem 6.6 | `thm:pi1-homotopy-invariant` | [`pi1EquivOfIsHomotopyEquiv`](Course/Week06Invariance.lean#L417-L422) |
| Corollary 6.7 | `cor:contractible-sc` | [`Contractible.simplyConnected`](Course/Week06Invariance.lean#L450-L467) |
| Proposition 6.8 | `prop:pi1-product` | [`pi1Prod`](Course/Week06Invariance.lean#L545-L552) |
| Proposition 6.9 | `prop:evenly-covered` | [`continuous_sec`](Course/Week06.lean#L256-L275), [`p_eq_iff_of_mem_arc`](Course/Week06.lean#L277-L290) |
| Lemma 6.10 | `lem:integer-difference` | [`lift_eq_of_preconnected`](Course/Week06.lean#L434-L489) |
| Definition 6.11 | `def:evenly-covered` | [`EvenlyCovered`](Course/Week07Covering.lean#L80-L90) |
| Definition 6.12 | `def:lift-circle` | [`IsLift`](Course/Week06.lean#L294-L299) |
| Theorem 6.13 | `thm:path-lifting` | [`exists_lift_path`](Course/Week06.lean#L640-L667), [`lift_path_unique`](Course/Week06.lean#L669-L675) |
| Theorem 6.14 | `thm:homotopy-lifting` | [`exists_lift_homotopy`](Course/Week06.lean#L711-L804), [`lift_homotopy_unique`](Course/Week06.lean#L806-L810), [`lift_edge_const`](Course/Week06.lean#L812-L821) |
| Definition 6.15 | `def:degree-circle` | [`degLoop`](Course/Week06.lean#L862-L867) |
| Theorem 6.16 | `thm:pi1-circle` | [`pi1Circle`](Course/Week06.lean#L1029-L1047), [`pi1Circle_windLoop_one`](Course/Week06.lean#L1053-L1056) |
| Corollary 6.17 | `cor:circle-consequences` | [`pi1Torus`](Course/Week06Circle.lean#L82-L87), [`S1_not_homotopyEquivalent_torus`](Course/Week06Circle.lean#L136-L145), [`pi1Cylinder`](Course/Week06Circle.lean#L193-L204), [`pi1Plane0`](Course/Week06Circle.lean#L332-L335) |
| Proposition 6.19 | `prop:retract-pi1` | [`retract_pi1`](Course/Week06Brouwer.lean#L209-L229) |
| Theorem 6.21 | `thm:no-retraction-2` | [`no_retraction_D2`](Course/Week06Brouwer.lean#L328-L356) |
| Corollary 6.22 | `cor:brouwer-from-retraction` | [`Brouwer.ray_mem`](Course/Week06Brouwer.lean#L433-L436), [`Brouwer.ray_of_mem_S1`](Course/Week06Brouwer.lean#L438-L459), [`Brouwer.continuous_ray`](Course/Week06Brouwer.lean#L469-L489) |
| Corollary 6.23 | `cor:brouwer-2` | [`brouwer_D2`](Course/Week06Brouwer.lean#L493-L520) |
| Exercise 6.E3 | `exr-6-basepoint` | [`beta_congr`](Course/Week06Invariance.lean#L147-L152), [`beta_refl`](Course/Week06Invariance.lean#L154-L159), [`beta_trans`](Course/Week06Invariance.lean#L161-L169) |
| Homework 6.H3 | `hw-6-3` | [`Path.pmul_homotopic_trans`](Course/Week03Hot.lean#L597-L601), [`pi1_mul_comm`](Course/Week03Hot.lean#L603-L613) |
| Theorem 7.1 | `thm:generation` | [`generation_groupoid`](Course/Week07Spheres.lean#L257-L401), [`generation`](Course/Week07Spheres.lean#L403-L455) |
| Theorem 7.3 | `thm:spheres-sc` | [`spheres_simplyConnected`](Course/Week07Spheres.lean#L648-L690) |
| Corollary 7.4 | `cor:s2-not-s1-t2` | [`sphere_not_homeomorph_S1`](Course/Week07Spheres.lean#L805-L811), [`sphere_not_homeomorph_Torus`](Course/Week07Spheres.lean#L813-L832), [`eq_of_Torus_homeomorph`](Course/Week07Spheres.lean#L834-L848) |
| Corollary 7.5 | `cor:R2-R3` | [`R2_not_homeomorph_Rn_of_ne`](Course/Week07Spheres.lean#L1003-L1015) |
| Proposition 7.6 | `prop:nonsurjective-nullhomotopic` | [`nullhomotopic_of_not_surjective`](Course/Week07Spheres.lean#L1019-L1040) |
| Theorem 7.7 | `thm:sk-sn` | [`loop_nullhomotopic`](Course/Week07Spheres.lean#L692-L699), [`sk_sn_nullhomotopic`](Course/Week07Spheres.lean#L1272-L1323) |
| Remark 7.8 | `rem:which-route` | [`exists_differentiable_near`](Course/Week07Spheres.lean#L1091-L1136), [`exists_not_mem_normalize`](Course/Week07Spheres.lean#L1202-L1270) |
| Definition 7.9 | `def:mapping-cylinder` | [`MappingCylinder`](Course/Week07Covering.lean#L1298-L1301) |
| Proposition 7.10 | `prop:mapping-cylinder` | [`mappingCylinder_deformationRetract`](Course/Week07Covering.lean#L1321-L1363) |
| Proposition 7.11 | `prop:degree` | [`degree_eq_of_homotopic`](Course/Week07Degree.lean#L144-L187), [`degree_comp`](Course/Week07Degree.lean#L278-L284), [`degreeHot_bijective`](Course/Week07Degree.lean#L295-L310), [`surjective_of_degree_ne_zero`](Course/Week07Degree.lean#L354-L362) |
| Definition 7.12 | `def:winding-number` | [`winding`](Course/Week07Degree.lean#L763-L765) |
| Proposition 7.13 | `prop:winding` | [`winding_eq_of_homotopy`](Course/Week07Degree.lean#L772-L791), [`winding_eq_of_joinedOff`](Course/Week07Degree.lean#L943-L950), [`exists_unique_unbounded_component`](Course/Week07Degree.lean#L1007-L1039), [`winding_eq_zero_of_unbounded`](Course/Week07Degree.lean#L1041-L1073) |
| Theorem 7.14 | `thm:fta` | [`fta`](Course/Week07Degree.lean#L584-L600) |
| Lemma 7.15 | `lem:odd-degree` | [`degree_odd`](Course/Week07Degree.lean#L613-L660) |
| Theorem 7.16 | `thm:borsuk-ulam-2` | [`borsuk_ulam_2`](Course/Week07Degree.lean#L687-L754) |
| Definition 7.17 | `def:covering-map` | [`IsCovering`](Course/Week07Covering.lean#L92-L96), [`IsCovering.discrete_fibre`](Course/Week07Covering.lean#L165-L187) |
| Lemma 7.18 | `lem:unique-lift` | [`IsCovering.eq_of_lift`](Course/Week07Covering.lean#L191-L234) |
| Theorem 7.19 | `thm:lifting-general` | [`IsCovering.exists_lift_path`](Course/Week07Covering.lean#L490-L509), [`IsCovering.lift_path_unique`](Course/Week07Covering.lean#L511-L516), [`IsCovering.exists_lift_homotopy`](Course/Week07Covering.lean#L550-L651), [`IsCovering.lift_edge_const`](Course/Week07Covering.lean#L661-L671) |
| Corollary 7.20 | `cor:nonclosed-lift` | [`IsCovering.mk_ne_one_of_lift`](Course/Week07Covering.lean#L673-L709) |
| Definition 7.22 | `def:fibration` | [`IsLocallyTrivial`](Course/Week07Covering.lean#L719-L729) |
| Lemma 7.23 | `lem:pullback-fibration` | [`IsLocallyTrivial.pullback`](Course/Week07Covering.lean#L731-L792), [`IsCovering.pullback`](Course/Week07Covering.lean#L794-L871), [`pullback_fibre`](Course/Week07Covering.lean#L874-L901) |
| Lemma 7.24 | `lem:covering-interval` | [`section_eq_const`](Course/Week07Covering.lean#L903-L923), [`IsCovering.trivial_over_I`](Course/Week07Covering.lean#L969-L1172) |
| Definition 7.25 | `def:universal-cover` | [`IsUniversalCover`](Course/Week07Covering.lean#L1256-L1261) |
| Exercise 7.E1 | `exr-6-antipodal` | [`homotopic_of_ne_neg`](Course/Week07Spheres.lean#L1138-L1200) |
| Example 8.14 | `ex:familiar-presentations` | [`Presentations.cyc_equiv`](Course/Week08FreeGroups.lean#L195-L218), [`Presentations.tor_equiv`](Course/Week08FreeGroups.lean#L277-L295), [`Presentations.ab_infinite_order`](Course/Week08FreeGroups.lean#L329-L337) |
| Definition 8.15 | `def:free-abelian` | [`abEquiv`](Course/Week08FreeGroups.lean#L117-L126) |
| Proposition 8.16 | `prop:rank` | [`rank_unique`](Course/Week08FreeGroups.lean#L97-L103) |
| Exercise 8.E4 | `exr-8-free-rank` | [`free_rank`](Course/Week08FreeGroups.lean#L130-L139), [`subsingleton_of_comm`](Course/Week08FreeGroups.lean#L141-L153) |
| Exercise 8.E7 | `exr-8-pingpong` | [`PingPong.pingpong`](Course/Week08FreeGroups.lean#L387-L422) |
| Lemma 9.4 | `lem:boundaries-are-cycles` | [`range_le_ker`](Course/Week09Homology.lean#L65-L73) |
| Lemma 9.8 | `lem:chain-map-homology` | [`induced_map_exists_unique`](Course/Week09Homology.lean#L88-L133), [`functoriality`](Course/Week09Homology.lean#L135-L170) |
| Lemma 9.13 | `lem:chain-homotopy` | [`homotopic_maps_agree`](Course/Week09Homology.lean#L174-L209) |
| Definition 9.15 | `def:betti-euler` | [`b1_eq_edges_sub_vertices_add_one`](Course/Week09Homology.lean#L838-L861), [`b1_eq_edges_sub_vertices_add_components`](Course/Week09Homology.lean#L863-L876), [`euler_number_eq_alternating_dim`](Course/Week09Homology.lean#L1008-L1058) (proof after 12 November 2026) |
| Remark 9.16 | `rem:euler-chain-groups` | [`euler_number_eq_alternating_dim`](Course/Week09Homology.lean#L1008-L1058) (proof after 12 November 2026) |
| Example 9.18 | `ex:graph-cycles` | [`b0_eq_components`](Course/Week09Homology.lean#L733-L766) (proof after 12 November 2026), [`b1_eq_edges_sub_vertices_add_one`](Course/Week09Homology.lean#L838-L861) |
| Definition 9.20 | `def:standard-simplex` | [`Singular.Simplex`](Course/Week09Homology.lean#L298-L299) |
| Lemma 9.21 | `lem:face-identity` | [`delete_comm`](Course/Week09Homology.lean#L268-L275), [`Singular.face_comp`](Course/Week09Homology.lean#L325-L349) |
| Definition 9.23 | `def:boundary` | [`Singular.bd`](Course/Week09Homology.lean#L313-L318) |
| Lemma 9.24 | `lem:dd` | [`Singular.bd_bd`](Course/Week09Homology.lean#L351-L364) |
| Proposition 9.26 | `prop:H0` | [`H0_equiv_int`](Course/Week09Homology.lean#L500-L521), [`Singular.H0_equiv_int`](Course/Week09Homology.lean#L611-L641) |
| Proposition 9.29 | `prop:homology-point` | [`point_acyclic`](Course/Week09Homology.lean#L441-L445), [`point_H0`](Course/Week09Homology.lean#L523-L527) |
| Proposition 9.30 | `prop:cone-construction` | [`acyclic`](Course/Week09Homology.lean#L426-L439) |
| Exercise 9.E1 | `exr-9-graph` | [`b1_eq_edges_sub_vertices_add_components`](Course/Week09Homology.lean#L863-L876), [`GraphZ.H0_equiv`](Course/Week09Homology.lean#L894-L948) (proof after 12 November 2026) |
| Exercise 9.E2 | `exr-9-reduced` | [`vertexSum`](Course/Week09Homology.lean#L788-L790) |
| Homework 9.H4 | `hw-9-4` | [`connecting_map_exists_unique`](Course/Week09Homology.lean#L1184-L1247) (proof after 12 November 2026), [`zigzag_exact`](Course/Week09Homology.lean#L1305-L1447) (proof after 12 November 2026) |
| Homework 9.H9 | `hw-9-9` | [`euler_number_eq_alternating_dim`](Course/Week09Homology.lean#L1008-L1058) (proof after 12 November 2026) |
| Homework 9.H10 | `hw-9-10` | [`GraphZ.H0_equiv`](Course/Week09Homology.lean#L894-L948) (proof after 12 November 2026) |
| Theorem 10.16 | `thm:surface-groups` | [`Crosscap.crosscap_ab`](Course/Week10SurfaceGroups.lean#L210-L243) |
| Corollary 10.17 | `cor:surface-abelian` | [`surface_ab`](Course/Week10SurfaceGroups.lean#L76-L95) |
| Theorem 12.10 | `thm:deck-group` | [`deck_group`](Course/Week12Deck.lean#L170-L211) |
| Lemma 13.2 | `lem:mv-ses` | [`mv_ses`](Course/Week13MayerVietoris.lean#L52-L90) |
