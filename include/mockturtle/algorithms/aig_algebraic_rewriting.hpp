/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
      return true;
    if ( try_three_level_distributivity( n ) )
      return true;
    /* TODO: add more rules here... */

    return false;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    
    if ( ntk.is_on_critical_path( n ) == false )
    {
      return false;
    }

    //storage ordered child vectors
    std::vector<signal> sig_childs;     // vector to store the children signals
    std::vector<node> node_childs;      // vector to store the children nodes
    std::vector<uint32_t> level_childs; // vector to store the levels

    //storage ordered nephew vectors
    std::vector<signal> sig_nephews;     // vector to store the nephew signals
    std::vector<node> node_nephews;      // vector to store the nephew nodes
    std::vector<uint32_t> level_nephews; // vector to store the levels

    //Exit variable
    bool exit{ false };

    //flag for circuit modification
    bool changes{ false };

    ntk.foreach_fanin( n, [&]( signal const& sig ) 
                       {
                         node children_node = ntk.get_node( sig ); 
                         signal children_sig = sig;
                         uint32_t children_lv = ntk.level( children_node );

                         // I fill vectors containing nodes signals and levels
                         sig_childs.emplace_back( children_sig );
                         node_childs.emplace_back( children_node );
                         level_childs.emplace_back( children_lv );
                       } );

    if ( ( sig_childs.size() != 2 ) || ( node_childs.size() != 2 ) || ( level_childs.size() != 2 ))
    {
      // I check that the vectors has got the correct size
      //the size should be 2
      exit = true;
      return false;
    }

    // The nodes with HIGHEST LEVEL is on the LEFT
    if ( level_childs[1] > level_childs[0] )
    {
      std::swap( sig_childs[0], sig_childs[1] );
      std::swap( node_childs[0], node_childs[1] );
      std::swap( level_childs[0], level_childs[1] );
    }

    //check on levels
    if ( ( level_childs[0] - level_childs[1] ) < 2 )
    {
      //No advantage in performing associativity if the difference in depth is less than 2
      exit = true;
      return false;
    }
    //only the child 0 can be on critical path
    if ( ( !ntk.is_on_critical_path(node_childs[0])) || (ntk.is_on_critical_path(node_childs[1])))
    {
      //If both operands are on critical path no associativity advantage
      //Same if both outside (this cond shouldn't happen)
      exit = true;
      return false;
    }

    // NOTE: The moving child must be sig_childs[1]
    
    if ( ntk.is_complemented( sig_childs[0] ) == true )
    {
      //No associativity on complemented signals on critical path
      //sig_child[0] must be on crit path
      exit = true;
      return false;
    }

    //I need to check the children of the signal on the critical path
    ntk.foreach_fanin( node_childs[0], [&]( signal const& sig_nep )
                       {
                         node nephew_node = ntk.get_node( sig_nep );
                         signal nephew_sig = sig_nep;
                         uint32_t nephew_lv = ntk.level( nephew_node );

                         //I fill the nephews vectors with nodes, signals and levels
                         sig_nephews.emplace_back( nephew_sig );
                         node_nephews.emplace_back( nephew_node );
                         level_nephews.emplace_back( nephew_lv );
                       } );

    // I check that the vectors has got the correct size
    if ( ( sig_nephews.size() != 2 ) || ( node_nephews.size() != 2 ) || ( level_nephews.size() != 2 ) )
    {
      //the size should be 2
      exit = true;
      return false;
    }

    // The nodes with HIGHEST LEVEL is set on the LEFT
    if ( level_nephews[1] > level_nephews[0] )
    {
      std::swap( sig_nephews[0], sig_nephews[1] );
      std::swap( node_nephews[0], node_nephews[1] );
      std::swap( level_nephews[0], level_nephews[1] );
    }

    if ( level_nephews[0] == level_nephews[1] )
    {
      //Only 1 signal can be on the critical path--> the signal can't have the same level
      exit = true;
      return false;
    }
    else
    {
      changes = true;
    }

    if ( exit )
    {
      return false;
    }
    else if ( changes == true )
    //If this flag is false and we arrive here the substitution should be done
    {
      //Here I create the two new AND and i substitute the old one
      signal bottom_and = ntk.create_and( sig_childs[1], sig_nephews[1] );
      signal top_and = ntk.create_and( bottom_and, sig_nephews[0] );
      ntk.substitute_node( n, top_and );
      return true;
    }
     
        return false;
  }
  //End associativity


  /* Try the distributivity rule on node n. Return true if the network is updated. */;
  bool try_distributivity( node n )
  {
    
    if ( ntk.is_on_critical_path( n ) == false )
    {
      return false;
    }

    //storage children vectors
    std::vector<signal> sig_childs;     // vector to store the children signals
    std::vector<node> node_childs;      // vector to store the children nodes
    std::vector<uint32_t> level_childs; // vector to store the levels

    //storage nephew vectors
    std::vector<signal> sig_nephews;     // vector to store the nephew signals
    std::vector<node> node_nephews;      // vector to store the nephew nodes
    std::vector<uint32_t> level_nephews; // vector to store the levels

    //storage nephew second vectors
    std::vector<signal> sig_nephews_s;     // vector to store the nephew signals
    std::vector<node> node_nephews_s;      // vector to store the nephew nodes
    std::vector<uint32_t> level_nephews_s; // vector to store the levels

    //Exit variable
    bool exit{ false };

    //flag for modification
    bool in_common{ false };

    ntk.foreach_fanin( n, [&]( signal const& sig )
                       {
                         node children_node = ntk.get_node( sig );
                         signal children_sig = sig;
                         uint32_t children_lv = ntk.level( children_node );


                         // I fill vectors containing nodes signals and levels
                         sig_childs.emplace_back( children_sig );
                         node_childs.emplace_back( children_node );
                         level_childs.emplace_back( children_lv );
                       } );

     // I check that the vectors has got the correct size
    if ( ( sig_childs.size() != 2 ) || ( node_childs.size() != 2 ) || ( level_childs.size() != 2 ))
    {
      //the size should be 2
      exit = true;
      return false;
    }

    // Both the inputs must be on the critical path
    if ( ( ntk.is_on_critical_path(node_childs[0]) == false ) || ( ntk.is_on_critical_path(node_childs[1]) == false ) )
    {
      exit = true;
      //I can't apply distributivity to PI
      return false;
    }

     // I can't reduce the delay if they are PI
     if ( ( level_childs[0] == 0) || ( level_childs[1] == 0 ) )
    {
      exit = true;
      //I can't apply distributivity to PI
      return false;
    }

     //Both signals need to be complemented
     if ( ( !ntk.is_complemented( sig_childs[0] ) ) || ( !ntk.is_complemented( sig_childs[1] ) ) )
    {
      exit = true;
      return false;
    }

    

    //Here I don't need to do the ordering since both are at the same level

    //Here I fill the  fitst nephew signals
    ntk.foreach_fanin( node_childs[0], [&]( signal const& sig_nep )
                       {
                         node nephew_node = ntk.get_node( sig_nep );
                         signal nephew_sig = sig_nep;
                         uint32_t nephew_lv = ntk.level( nephew_node );
                         //bool nephew_path = ntk.is_on_critical_path( nephew_node );

                         //I fill the vectors with nodes, signals and levels
                         sig_nephews.emplace_back( nephew_sig );
                         node_nephews.emplace_back( nephew_node );
                         level_nephews.emplace_back( nephew_lv );
                        // critical_nephews.emplace_back( nephew_path );
                       } );

    // I check that the vectors has got the correct size
    if ( ( sig_nephews.size() != 2 ) || ( node_nephews.size() != 2 ) || ( level_nephews.size() != 2 ) )
    {
      //the size should be 2
      exit = true;
      return false;
    }

    // The nodes with HIGHEST LEVEL is set on the LEFT
    if ( level_nephews[1] > level_nephews[0] )
    {
      std::swap( sig_nephews[0], sig_nephews[1] );
      std::swap( node_nephews[0], node_nephews[1] );
      std::swap( level_nephews[0], level_nephews[1] );
      //std::swap( critical_nephews[0], critical_nephews[1] );
    }

    //Only nephew 0 can be on critical path 
    if ( ( ntk.is_on_critical_path( node_nephews[0] ) == false ) || ( ntk.is_on_critical_path( node_nephews[1] ) == true ) )
    {
      exit = true;
      //I can't apply distributivity to PI
      return false;
    }
    
    // //The signal on critical path must be sig_nephew[0]

    //Here I fill the second nephew signals
    ntk.foreach_fanin( node_childs[1], [&]( signal const& sig_nep )
                       {
                         node nephew_s_node = ntk.get_node( sig_nep );
                         signal nephew_s_sig = sig_nep;
                         uint32_t nephew_s_lv = ntk.level( nephew_s_node );

                         //I fill the vectors with nodes, signals and levels
                         sig_nephews_s.emplace_back( nephew_s_sig );
                         node_nephews_s.emplace_back( nephew_s_node );
                         level_nephews_s.emplace_back( nephew_s_lv );
                       } );

    // I check that the vectors has got the correct size
    if ( ( sig_nephews_s.size() != 2 ) || ( node_nephews_s.size() != 2 ) || ( level_nephews_s.size() != 2 ) )
    {
      //the size should be 2
      exit = true;
      return false;
    }

    // The nodes with HIGHEST LEVEL is set on the LEFT
    if ( level_nephews_s[1] > level_nephews_s[0] )
    {
      std::swap( sig_nephews_s[0], sig_nephews_s[1] );
      std::swap( node_nephews_s[0], node_nephews_s[1] );
      std::swap( level_nephews_s[0], level_nephews_s[1] );
    }

    //Only nephew 0 can be on critical path
    if ( ( ntk.is_on_critical_path( node_nephews_s[0] ) == false ) || ( ntk.is_on_critical_path( node_nephews_s[1] ) == true ) )
    {
      exit = true;
      return false;
    }
    
    //The signal on critical path must be sig_nephew_s[0]

    //I check that both critical signals are equal
    if (( sig_nephews[0] == sig_nephews_s[0] ) && (level_nephews[0]==level_nephews_s[0]))
    {
      in_common = true;
    }

    if ( exit )
    {
      return false;
    }

    if ( in_common == true )
    {
      signal lower_and = ntk.create_and( !sig_nephews[1], !sig_nephews_s[1] );
      signal top_and = ntk.create_and( sig_nephews[0], !lower_and );
      ntk.substitute_node( n, !top_and );
      return true;
       
      
    }
     
    return false;
  }

  bool try_three_level_distributivity( node n )
  {
    
  if ( ntk.is_on_critical_path( n ) == false )
  {
    return false;
  }

  //storage children ordered vectors
  std::vector<signal> sig_childs;     // vector to store the children signals
  std::vector<node> node_childs;      // vector to store the children nodes
  std::vector<uint32_t> level_childs; // vector to store the levels

  //storage nephew  ordered vectors
  std::vector<signal> sig_nephews;     // vector to store the nephew signals
  std::vector<node> node_nephews;      // vector to store the nephew nodes
  std::vector<uint32_t> level_nephews; // vector to store the levels

  //storage grandnephew  ordered vectors
  std::vector<signal> sig_grand_nephews;     // vector to store the grandnephew signals
  std::vector<node> node_grand_nephews;      // vector to store the grandnephew nodes
  std::vector<uint32_t> level_grand_nephews; // vector to store the levels

  //Exit variable
  bool exit{ false }; // This variable is used for a second exit check
  bool change{ false };


  ntk.foreach_fanin( n, [&]( signal const& sig ) 
                     {
                       node children_node = ntk.get_node( sig );
                       signal children_sig = sig;
                       uint32_t children_lv = ntk.level( children_node );

                       // I fill vectors containing nodes signals and levels
                       sig_childs.emplace_back( children_sig );
                       node_childs.emplace_back( children_node );
                       level_childs.emplace_back( children_lv );
                     } );

  // I check that the vectors has got the correct size
  if ( ( sig_childs.size() != 2 ) || ( node_childs.size() != 2 ) || ( level_childs.size() != 2 ) )
  {
    //the size should be 2
    exit = true;
    return false;
  }

  // The nodes with HIGHEST LEVEL is on the LEFT
  if ( level_childs[1] > level_childs[0] )
  {
    std::swap( sig_childs[0], sig_childs[1] );
    std::swap( node_childs[0], node_childs[1] );
    std::swap( level_childs[0], level_childs[1] );
  }


  //check on levels
  if ( ( level_childs[0] - level_childs[1] ) < 3 )
  {
    //No advantage in performing associativity if the difference in depth is less than 2
    exit = true;
    return false;
  }

  //check on critical path and eventual assegnation
  if ( (ntk.is_on_critical_path( node_childs[0] )== false) || (ntk.is_on_critical_path( node_childs[1] )== true))
  {
    //node_childs[0] should be on critical path
    //node_childs[1] should be outside otherwise no advantage
    exit = true;
    return false;
  }
  

   
   // Three layer distributivity:  ((g x2) + x3 ) x4 = (g x2 x4) + (x3 x4) = (g (x2 x4)) + (x3 x4) 

  // NOTE : ordering the children vectors x4== sig_childs[1] 
  
  // x4 shouldn't be complemented< -- check in case it is not working

  // Crit path should be complemented
  if ( !ntk.is_complemented( sig_childs[0] ) )
  {
      //The operation cannot be performed
      exit = true;
      return false;
  }
  
  //I need to check the children of the signal on the critical path
  ntk.foreach_fanin( node_childs[0], [&]( signal const& sig_nep )
                     {
                       node nephew_node = ntk.get_node( sig_nep );
                       signal nephew_sig = sig_nep;
                       uint32_t nephew_lv = ntk.level( nephew_node );

                       //I fill the nephewsvectors with nodes, signals and levels
                       sig_nephews.emplace_back( nephew_sig );
                       node_nephews.emplace_back( nephew_node );
                       level_nephews.emplace_back( nephew_lv );

                     } );

  // I check that the vectors has got the correct size
  if ( ( sig_nephews.size() != 2 ) || ( node_nephews.size() != 2 ) || ( level_nephews.size() != 2 ) )
  {
    //the size should be 2
    exit = true;
    return false;
  }

   // The nodes with HIGHEST LEVEL is set on the LEFT
  if ( level_nephews[1] > level_nephews[0] )
  {
    std::swap( sig_nephews[0], sig_nephews[1] );
    std::swap( node_nephews[0], node_nephews[1] );
    std::swap( level_nephews[0], level_nephews[1] );
  }

   //Both the nephew signals has to be complemented
  if (( !ntk.is_complemented( sig_nephews[0] ) ) || ( !ntk.is_complemented( sig_nephews[1] ) ))
  {
    //Otherwise the property can't be applied
    exit = true;
    return false;
  }
   
   // Three layer distributivity:  ((g x2) + x3 ) x4 = (g x2 x4) + (x3 x4) = (g (x2 x4)) + (x3 x4) 

  // NOTE : ordering the children vectors x3== sig_nephews[1]
  // x3 remains at the same depth 

  //x3 shouldn't be on the critical path --> otherwise no advantage to reduce g depth
  if ( ntk.is_on_critical_path(node_nephews[1] ) == true )
  {
      // the only allowed combination is crit[0]=true crit[1]=false (since ordered
      exit = true;
      return false;
  }

  // I check at the third level on the critical gate
  ntk.foreach_fanin( node_nephews[0], [&]( signal const& sig_gnep )
                     {
                       node grand_nephew_node = ntk.get_node( sig_gnep );
                       signal grand_nephew_sig = sig_gnep;
                       uint32_t grand_nephew_lv = ntk.level( grand_nephew_node );

                       //I fill the nephewsvectors with nodes, signals and levels
                       sig_grand_nephews.emplace_back( grand_nephew_sig );
                       node_grand_nephews.emplace_back( grand_nephew_node );
                       level_grand_nephews.emplace_back( grand_nephew_lv );

                     } );

  // I check that the vectors has got the correct size
  if ( ( sig_grand_nephews.size() != 2 ) || ( node_grand_nephews.size() != 2 ) || ( level_grand_nephews.size() != 2 ) )
  {
    //the size should be 2
    exit = true;
    return false;
  }

  // The nodes with HIGHEST LEVEL is set on the LEFT
  if ( level_grand_nephews[1] > level_grand_nephews[0] )
  {
    std::swap( sig_grand_nephews[0], sig_grand_nephews[1] );
    std::swap( node_grand_nephews[0], node_grand_nephews[1] );
    std::swap( level_grand_nephews[0], level_grand_nephews[1] );
  }


  if ( ntk.is_on_critical_path(node_grand_nephews[1]) == true ) 
  {
    // the only allowed combination is crit[0]=true crit[1]=false
    exit = true;
    return false;
  }
  else
  {
    change = true;
  }

   // Three layer distributivity:  ((g x2) + x3 ) x4 = (g x2 x4) + (x3 x4) = (g (x2 x4)) + (x3 x4) 

  // NOTE : ordering the children vectors x2== sig_grand_nephews[1]
  // g==sig_grand_nephews[0]

  if ( exit )
  {
    return false;
  }
  

  if (change==true)
  {
    signal x3_and_x4 = ntk.create_and( !sig_nephews[1], sig_childs[1] );
    signal x2_and_x4 = ntk.create_and( sig_grand_nephews[1], sig_childs[1] );
    signal g_and_x2x4 = ntk.create_and( sig_grand_nephews[0], x2_and_x4 );
    signal top_node = ntk.create_and( !g_and_x2x4, !x3_and_x4 );
    ntk.substitute_node( n, !top_node );
    return true;
  }
  
    return false;
  }

private:
  Ntk& ntk;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */