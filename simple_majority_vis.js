const candies = Candidate
const voties = SimpleMajorityVoter
const candy_url1 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/candidate1.svg'
const candy_url2 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/candidate2.svg'
const candy_url3 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/candidate3.svg'
const candy_url4 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/candidate4.svg'

const voter_url1 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/voter1.svg'
const voter_url2 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/voter2.svg'
const voter_url3 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/voter3.svg'
const voter_url4 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/voter4.svg'
const voter_url5 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/voter5.svg'
const voter_url6 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/voter6.svg'
const voter_url7 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/voter7.svg'
const voter_url8 = '/Users/juliamccauley/Desktop/cs1710/projects/arrows_impossibility_theorem/vis_resources/voter8.svg'

const candy_url_arr = [candy_url1, candy_url2, candy_url3, candy_url4]
const voter_url_arr  = [voter_url1, voter_url2, voter_url3, voter_url4, voter_url5, voter_url6, voter_url7, voter_url8]

div.replaceChildren() // remove all content


function get_first_choice_candidate(my_voter) {
    const ans = my_voter.join(firstChoice).toString(); 
    return ans; 
}

function make_candy(url, my_candidate) {
  const cand_plat = document.createElement('div')
  cand_plat.style.width = '100%'
  cand_plat.style.height = '100%'
  cand_plat.style.display = 'inline'
  const img = document.createElement('img')
  img.src = url
  img.style.width = '20%'
  img.style.height = '20%'
  img.style['margin-top'] = '5%'
  img.style['margin-bottom'] = '5%'
  const cand_label = document.createElement("p")
  cand_label.innerText = my_candidate.toString()
  cand_plat.appendChild(cand_label)

//   const test_thing = document.createElement('img')
//   const test_icon = voter_url_arr[1]
//   test_thing.src = test_icon
//   test_thing.style.width = '10%'
//   test_thing.style.height = '10%'
//   cand_plat.appendChild(test_thing)

  console.log("hello I am here :DDDD")
  cand_plat.appendChild(img)

  for (const my_ind in voties.tuples()) { //add voters for the candidate
    const votie = voties.tuples()[my_ind]
    const voter_FC = get_first_choice_candidate(votie)
    if(voter_FC == my_candidate.toString()) {
        const icon = voter_url_arr[my_ind%7]
        const voter_img = document.createElement('img')
        voter_img.src = icon
        voter_img.style.width = '10%'
        voter_img.style.height = '10%'
        voter_img.style.display = 'inline'
        if(voter_FC != votie.join(secretPreference).toString()) {
            voter_img.style["background-color"] = 'yellow'    
        }
        cand_plat.appendChild(voter_img)
    }  
  }
  
  return cand_plat
}


function make_election() {
    const div = document.createElement('div')
    div.style.width = '100%'
    div.style.height = '70%'
    
    for (const ind in candies.tuples()) {
      const candie = candies.tuples()[ind]
      const icon = candy_url_arr[ind%3]
      div.appendChild(make_candy(icon, candie))
    }
      
    return div
    
  }

const my_election = document.createElement('div')
my_election.style.width = '100%'
my_election.style.height = '50%'
my_election.style.margin = '1%'
my_election.style.marginRight = '0'
my_election.style.padding = '0.5em'
my_election.style.border = '1px solid black'
my_election.style.display = 'inline-block'
my_election.style.color = 'black'
my_election.style["background-color"] = '#61e3fa'

my_election.appendChild(make_election())
div.appendChild(my_election)